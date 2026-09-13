-- PINNING THE MAP FRAME'S BOUND IS NOT ENOUGH WHILE BOTH ENDS ARE
-- PINNED AT THE SAME PLACE, AND APPLYING THE TEMPLATE TWICE IS WHY.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.

-- WHAT THIS TESTS, AND WHY IT IS THE NEXT THING TO TEST.  The frame
-- predicate's payload bound used to be quantified over every natural,
-- and a template that drops its argument is false there — the finding
-- being that the walk instantiates at exactly ONE bound, the reading of
-- the whole map expression.  The obvious repair is to PIN the statement
-- at that bound.  The call site pins BOTH ends at it, because what it
-- has about the incoming burst is a reading of the SOURCE which it then
-- widens to the map's.  This file is that repair, refuted.

-- THE TEMPLATE THAT DOES IT WRAPS ITS ARGUMENT INSTEAD OF DROPPING IT.
-- One application adds a layer, so the map expression's reading is the
-- source's plus that layer — and a payload the widened bound ADMITS is
-- one that already carries the layer.  Feed the frame what the whole
-- expression emits and the template adds a second: the hypothesis holds
-- at the pinned bound and the conclusion misses it by exactly one, at a
-- payload REACHED BY RUNNING rather than written down.

-- SO THE REPAIR IS ASYMMETRY, NOT A TIGHTER PIN.  The two bounds are
-- readings of DIFFERENT expressions — what comes in is the source's and
-- what goes out is the map's — and collapsing them to the larger one
-- hands the frame an input the source could never emit.  The widening
-- that produces the collapse is available at the call site and is not
-- needed there: what the recursion returns about the inner burst is
-- already stated at the source's own reading.
module Refuted.Map-Pinned where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick; InstEvent)
open import Rx.Exp using (Ctx; Closed; Exp; Ty; Val; Fn; natᵗ; obs; strmᵗ;
  ofᵉ; mergeAllᵉ; mapᵉ; nat̂; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃; depthᵛ; depthᵉ)
open import Rx.Evaluator using (Path; Frame; Stream; Sched; EvalSt; root;
  map-f; stepFrame; subscribeE; rootWitness; sched-init; st-init;
  splitBurst; stHop)

----------------------------------------------------------------------
-- THE CURRENCY, WRITTEN OUT HERE RATHER THAN IMPORTED.  The claim is
-- about a predicate whose whole content is which bound stands on which
-- side, so a repair that moves a bound must make these rows fail by
-- name rather than quietly agree with them.
----------------------------------------------------------------------

valsHop′ : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (u : Ty) → List (Val Γ u) → ℕ
valsHop′ ψ u []       = 0
valsHop′ ψ u (v ∷ vs) = depthᵛ ψ u v ⊔ valsHop′ ψ u vs

FrameCarries′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo} →
  Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ lo u t →
  (Fin n → Rd₃) → ℕ → ℕ → ℕ → Set
FrameCarries′ {Γ = Γ} {e = e} {s = s} {u = u} ac id now f κ ψ Rin Rv Rst =
  ∀ (vals : List (Val Γ s)) (fin : Bool) (sd : Sched Γ) (st : EvalSt e) →
    valsHop′ ψ s vals ≤ Rin → stHop ψ st ≤ Rst →
    valsHop′ ψ u (proj₁ (stepFrame ac id now f κ vals fin sd st)) ≤ Rv
    × stHop ψ (proj₂ (proj₂ (proj₂ (proj₂
        (stepFrame ac id now f κ vals fin sd st))))) ≤ Rst

-- BOTH ENDS AT THE MAP EXPRESSION'S OWN READING, which is what the
-- walk supplies today and what the previous witness's finding was read
-- as licensing
MapFramePinned : Set
MapFramePinned = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
  (b : Exp Γ [] [] [] s) (κ : Path Γ lo u t) (ψ : Fin n → Rd₃) (Rst : ℕ) →
  FrameCarries′ {e = e} ac id now (map-f fn) κ ψ
    (depthᵉ ψ (mapᵉ fn b)) (depthᵉ ψ (mapᵉ fn b)) Rst

----------------------------------------------------------------------
-- THE WITNESS.  An empty context, so the reading has no slot to blame.
-- The template WRAPS its argument, which is the one thing the previous
-- witness's template did not do.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ ()

ψ₀ : Fin 0 → Rd₃
ψ₀ ()

-- re-wraps what it is given: the output is the argument under one more
-- flattener, so the reading rises by exactly the layer the map clause
-- charges for
grow : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
grow = strmᵗ (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ [])))

-- a single observable, as shallow as the type allows
src₀ : Exp Γ₀ [] [] [] (obs natᵗ)
src₀ = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

prog : Closed Γ₀ (obs natᵗ)
prog = mapᵉ grow src₀

ac₀ : Acc _≺_ _
ac₀ = rootWitness prog ins₀

----------------------------------------------------------------------
-- THE PAYLOAD IS REACHED BY RUNNING THE WHOLE EXPRESSION, not written
-- down: these are values the walk itself produces at this program, and
-- the pinned bound is exactly what admits them.
----------------------------------------------------------------------

r : Stream Γ₀ (obs natᵗ) × Sched Γ₀ × EvalSt prog
r = subscribeE {lo = 0} ac₀ prog root 0 0 (sched-init prog ins₀) (st-init prog)

sp : List (Val Γ₀ (obs natᵗ))
   × List (InstEvent (Val Γ₀ (obs natᵗ))) × Bool
sp = splitBurst (proj₁ r)

vals : List (Val Γ₀ (obs natᵗ))
vals = proj₁ sp

out : List (Val Γ₀ (obs natᵗ))
out = proj₁ (stepFrame {lo = 0} {e = prog} ac₀ 0 0 (map-f grow) root vals
               false (sched-init prog ins₀) (st-init prog))

----------------------------------------------------------------------
-- THE FIGURES.  Both sides are pinned, because the `⊥` below turns on
-- their ORDER and a repair that moved either would otherwise leave this
-- witness quiet.
----------------------------------------------------------------------

-- LOAD-BEARING: the pinned bound, which is the source's reading plus
-- the layer the template writes.  A repair that stopped charging for
-- the template would send this to zero and the crossing with it
pin-bound-is : depthᵉ ψ₀ (mapᵉ grow src₀) ≡ 1
pin-bound-is = refl

-- LOAD-BEARING: what the whole expression emits reads at exactly the
-- pinned bound, so the hypothesis is satisfied with NO margin — this is
-- the row that says the payload is admissible rather than invented
pin-in-is : valsHop′ ψ₀ (obs natᵗ) vals ≡ 1
pin-in-is = refl

-- LOAD-BEARING: and one more application of the same template puts the
-- output a whole layer past the bound both ends were pinned at
pin-out-is : valsHop′ ψ₀ (obs natᵗ) out ≡ 2
pin-out-is = refl

-- LOAD-BEARING: the store is untouched by a map frame, so the second
-- conjunct is satisfied and the crossing is the payload one alone
pin-store-is : stHop ψ₀ (st-init prog) ≡ 0
pin-store-is = refl

map-frame-pinned-false : MapFramePinned → ⊥
map-frame-pinned-false h
  with proj₁ (h {e = prog} {lo = 0} ac₀ 0 0 grow src₀ root ψ₀ 0 vals false
                (sched-init prog ins₀) (st-init prog)
                ≤-refl _≤_.z≤n)
... | _≤_.s≤s ()

----------------------------------------------------------------------
-- AND THE ASYMMETRIC FORM IS NOT TOUCHED BY THIS, PINNED SO THE
-- WITNESS CANNOT BE READ AS KILLING THE REPAIR IT POINTS AT.  Held to
-- the SOURCE's reading on the way in, the payload above is out of
-- scope — it reads one where the source reads zero — and what the
-- source really emits still lands under the map's reading on the way
-- out.  So the two bounds have to come apart; they do not have to move.
----------------------------------------------------------------------

ac₀′ : Acc _≺_ _
ac₀′ = rootWitness src₀ ins₀

r′ : Stream Γ₀ (obs natᵗ) × Sched Γ₀ × EvalSt src₀
r′ = subscribeE {lo = 0} ac₀′ src₀ root 0 0 (sched-init src₀ ins₀) (st-init src₀)

sp′ : List (Val Γ₀ (obs natᵗ))
    × List (InstEvent (Val Γ₀ (obs natᵗ))) × Bool
sp′ = splitBurst (proj₁ r′)

srcOut : List (Val Γ₀ (obs natᵗ))
srcOut = proj₁ (stepFrame {lo = 0} {e = src₀} ac₀′ 0 0 (map-f grow) root
                  (proj₁ sp′) false
                  (sched-init src₀ ins₀) (st-init src₀))

-- LOAD-BEARING: the source's own reading, which is where the incoming
-- bound belongs and which the refuting payload exceeds.  Zero, so the
-- two bounds are as far apart as this program can put them
pin-source-is : depthᵉ ψ₀ src₀ ≡ 0
pin-source-is = refl

-- LOAD-BEARING: the template applied to what the source ACTUALLY emits
-- lands under the map's reading, TIGHTLY — so the asymmetric statement
-- is not refuted at the very program that refutes the symmetric one,
-- and a repair that widened the outgoing bound would leave this row
-- agreeing with a claim nothing had tested
pin-asym-fits : valsHop′ ψ₀ (obs natᵗ) srcOut ≤ depthᵉ ψ₀ (mapᵉ grow src₀)
pin-asym-fits = ≤-refl
