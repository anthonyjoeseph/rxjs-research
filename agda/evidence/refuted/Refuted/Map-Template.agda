-- A MAP FRAME DOES NOT HAND BACK WHAT IT WAS HANDED, AND ITS TEMPLATE
-- IS WHY.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.

-- WHAT THE FRAME PREDICATE ASKS FOR.  A frame is said to CARRY when its
-- outputs read under the bound its inputs were held to and the store it
-- leaves reads under the bound the store came in at.  Four of the walk's
-- operators are claimed to carry with the two payload bounds EQUAL —
-- what goes in bounds what comes out — and the flattener is the one
-- exception, afforded a single `suc` for the hop it performs.

-- AND A TEMPLATE IS A THIRD SOURCE OF DEPTH THAT NEITHER BOUND READS.
-- A map's outputs are its template evaluated at the payload, and a
-- template may IGNORE its argument: the one below drops a numeral and
-- returns a flattener over a literal, which reads one where the numeral
-- read zero.  So the equal-bounds form is false by a whole hop at inputs
-- carrying no observable at all, and the gap is not a rate — it is
-- whatever the template writes, which is unbounded in the frame's own
-- size while both bounds stay at zero.

-- WHICH IS WHY THIS IS A SHAPE FINDING AND NOT A FALSITY ONE, AND THE
-- RESTATEMENT IS ALREADY WRITTEN DOWN ELSEWHERE.  The chain measure
-- spends the term reading's own map step at a `map-f` frame — the step
-- that reads the template against its argument — so the bound the frame
-- hands back is that step applied to the bound it was handed, never the
-- bound itself.  The two non-flattening frames are therefore not one
-- shelf: a take really does hand back a prefix of its input, and only
-- the map has a second thing to read.
module Refuted.Map-Template where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_; _≤_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick)
open import Rx.Exp using (Ctx; Closed; Exp; Ty; Val; Fn; natᵗ; obs; strmᵗ;
  ofᵉ; emptyᵉ; mergeAllᵉ; nat̂)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃; depthᵛ)
open import Rx.Evaluator using (Path; Frame; Sched; EvalSt; root; map-f;
  stepFrame; rootWitness; sched-init; st-init; stHop)

----------------------------------------------------------------------
-- THE CURRENCY, WRITTEN OUT HERE RATHER THAN IMPORTED.  The claim is
-- about a predicate whose whole content is which bound stands on which
-- side, so a repair that moves a bound must make these rows fail by
-- name rather than quietly agree with them.
----------------------------------------------------------------------

valsHop′ : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (u : Ty) → List (Val Γ u) → ℕ
valsHop′ ψ u []       = 0
valsHop′ ψ u (v ∷ vs) = depthᵛ ψ u v ⊔ valsHop′ ψ u vs

FrameCarries′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} →
  Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ u t →
  (Fin n → Rd₃) → ℕ → ℕ → ℕ → Set
FrameCarries′ {Γ = Γ} {e = e} {s = s} {u = u} ac id now f κ ψ Rin Rv Rst =
  ∀ (vals : List (Val Γ s)) (fin : Bool) (sd : Sched Γ) (st : EvalSt e) →
    valsHop′ ψ s vals ≤ Rin → stHop ψ st ≤ Rst →
    valsHop′ ψ u (proj₁ (stepFrame ac id now f κ vals fin sd st)) ≤ Rv
    × stHop ψ (proj₂ (proj₂ (proj₂ (proj₂
        (stepFrame ac id now f κ vals fin sd st))))) ≤ Rst

MapFrameCarried : Set
MapFrameCarried = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
  (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rv Rst : ℕ) →
  FrameCarries′ {e = e} ac id now (map-f fn) κ ψ Rv Rv Rst

----------------------------------------------------------------------
-- THE WITNESS.  An empty context, so the reading has no slot to blame;
-- a numeral in, an observable out, and the template never looks at what
-- it was given.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ ()

ψ₀ : Fin 0 → Rd₃
ψ₀ ()

-- a flattener over a one-element literal whose element is itself a
-- one-element literal: nothing is deferred, nothing is late, and the
-- hop is the flattener's own
deep : ∀ {Δᵍ Δ Θ} → Exp Γ₀ Δᵍ Δ Θ natᵗ
deep = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 5 ∷ [])) ∷ []))

-- drops its argument, which is the whole point: the input's reading
-- cannot bound an output the input did not contribute to
tmpl : Fn Γ₀ [] [] [] natᵗ (obs natᵗ)
tmpl = strmᵗ deep

root₀ : Closed Γ₀ (obs natᵗ)
root₀ = emptyᵉ

ac₀ : Acc _≺_ _
ac₀ = rootWitness root₀ ins₀

out : List (Val Γ₀ (obs natᵗ))
out = proj₁ (stepFrame {e = root₀} ac₀ 0 0 (map-f tmpl) root (0 ∷ [])
               false (sched-init root₀ ins₀) (st-init root₀))

----------------------------------------------------------------------
-- THE FIGURES.  Both sides are pinned, because the `⊥` below turns on
-- their ORDER and a repair that moved either would otherwise leave this
-- witness quiet.
----------------------------------------------------------------------

-- LOAD-BEARING: the payload carries no observable, so the bound the
-- frame is held to is zero and the statement is at its strongest
in-is : valsHop′ {Γ = Γ₀} ψ₀ natᵗ (0 ∷ []) ≡ 0
in-is = refl

-- LOAD-BEARING: the template's flattener, read off the value the frame
-- actually produced rather than off the term
out-is : valsHop′ ψ₀ (obs natᵗ) out ≡ 1
out-is = refl

-- LOAD-BEARING: the store is untouched by a map frame, so the second
-- conjunct is satisfiable and the crossing is the first one alone
store-is : stHop ψ₀ (st-init root₀) ≡ 0
store-is = refl

map-frame-carried-false : MapFrameCarried → ⊥
map-frame-carried-false h
  with proj₁ (h {e = root₀} ac₀ 0 0 tmpl root ψ₀ 0 0 (0 ∷ []) false
                (sched-init root₀ ins₀) (st-init root₀)
                (_≤_.z≤n) (_≤_.z≤n))
... | ()
