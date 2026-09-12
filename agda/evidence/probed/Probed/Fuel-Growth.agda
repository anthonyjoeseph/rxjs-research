-- THE ACCUMULATOR DEEPENS ONE PER ARRIVAL, WHICH IS THE RATE AN ENTRY
-- SEED HAS TO READ.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: drain-dry-free @140a87
--
-- WHAT THE SIBLING ROWS LEFT OPEN.  The seed rows put a fold's carried
-- nesting beside the rank the machine seeds and found the margin
-- widening: three deliveries against `2 ^ 14`, six against `2 ^ 17`, one
-- layer bought by one doubling.  Every one of those rows moved the
-- SOURCE, which is syntax, so every one of them moved both sides.  The
-- question they could not ask is what happens when the thing that moves
-- is not syntax at all.
--
-- ONE PROGRAM, SIX FUELS.  The source here is a recursion rather than a
-- literal, so the number of deliveries is set by the DRAIN and not by
-- the term: the program is twenty symbols and reads two at every row
-- below, the rank the ROOT is seeded at is `2 ^ 20` at every row below,
-- and the carried nesting is the fuel plus one.  One layer per unit of
-- fuel, against a root seed that is constant in it.
--
-- SO A SEED READ OFF THE PROGRAM ALONE DOES NOT BOUND THIS, and that is
-- a statement about every such seed rather than about this one.  The
-- accumulator is stored across arrivals and deepened by one at each, the
-- arrivals are paid for out of fuel, and fuel appears in neither `sizeᵉ`
-- nor `slotsSize` — so for a fixed program the readings are unbounded
-- while a program-only rank stands still.
--
-- WHICH IS WHY AN ENTRY IS NO LONGER TAKEN OFF THE PROGRAM ALONE.  A
-- cascade re-seeds per arrival, at the value it carries joined with the
-- store's own reading, and that reading takes a scan node to be its
-- accumulator — the quantity these rows measure.  So the rate they
-- establish is one the entry now tracks, and tracks exponentially: one
-- layer buys one doubling.  These rows are both the reason the reading
-- is there and the check that it moves at the rate it must.
--
-- WHERE THE CROSSING IS STILL REACHED.  Nothing above says the OPERATOR
-- shelf is paid for: it is handed an arbitrary triple satisfying the
-- entry invariant rather than one the machine minted, so no re-seed
-- reaches it.  `Refuted.Rank-Fold` holds the rank at that invariant's
-- own tightest and reaches the dry close in two deliveries, off a
-- literal source with the store reading zero.
--
-- WHAT IS NOT COVERED, AND IT IS WHERE THE DRAIN LEAF IS STILL OPEN.
-- One delivery lands per arrival here, so every layer counted below is
-- paid for by a fresh entry; no row reaches a burst delivering many
-- times inside ONE cascade, which is the growth no entry sees however it
-- is denominated.  One recursion shape and one flattening layer in the
-- step; the fuels are small because each row re-walks the whole drain,
-- so what is established is the RATE.  The `Confirms` rows sit at the
-- root, where the reading is seven against `2 ^ 20`.
module Probed.Fuel-Growth where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_; _^_; _⊔_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; sizeᵉ;
  ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; μᵉ; varᵉ; deferᵉ;
  strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator using (Stream; Sched; EvalSt; drain; subscribeE;
  rootWitness; root; sched-init; st-init)
open import Rx.Nest-Depth using (nestDᵉ)
open import Verify-Rank-Sufficient using (drain-dry-free)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- The two quantities the rows put side by side: how deep the values a
-- run hands out read, and what the ROOT is seeded at — the arrival's own
-- entry adds a reading this does not take, which is the point the rows
-- make.  Both are the sibling probe's, so a row here is comparable with
-- a row there.
----------------------------------------------------------------------

evNest : ∀ {n} {Γ : Ctx n} {u} → List (InstEvent (Closed Γ u)) → ℕ
evNest []             = 0
evNest (value v ∷ es) = nestDᵉ v ⊔ evNest es
evNest (_ ∷ es)       = evNest es

carried : ∀ {n} {Γ : Ctx n} {u} → Stream Γ (obs u) → ℕ
carried []         = 0
carried (em ∷ ems) = evNest (InstEmit.events em) ⊔ carried ems

seed : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → ℕ
seed e sl = 2 ^ (sizeᵉ e + slotsSize sl)

entry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Stream Γ t × Sched Γ × EvalSt e
entry e ins = subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins) (st-init e)

-- the fuel is a PARAMETER here rather than a module constant, which is
-- the whole instrument: every other quantity a row names is fixed by
-- the program, and this is the one axis left to move
drainAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
drainAt f e ins = drain f 1 (proj₁ (proj₂ (entry e ins))) (proj₂ (proj₂ (entry e ins)))

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE PROGRAM.  The step hands its accumulator straight back inside one
-- flattening layer, so each application reads one deeper than the last;
-- the source is `repeat`, the smallest recursion that goes on
-- delivering, so how many applications happen is the drain's business
-- and not the term's.  Together they are the one shape where a run's
-- own output outgrows every reading of the program that produced it.
----------------------------------------------------------------------

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

recur : Closed Γ₀ natᵗ
recur = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

fold : Closed Γ₀ (obs natᵗ)
fold = scanᵉ step (strmᵗ emptyᵉ) recur

----------------------------------------------------------------------
-- THE FIXED SIDE.  Both readings of the term, and the rank the machine
-- seeds off them.  Every row below holds these three constant, which is
-- what makes the moving one mean something.
----------------------------------------------------------------------

_ : sizeᵉ fold ≡ 20                                    -- LOAD-BEARING
_ = refl

_ : nestDᵉ fold ≡ 2                                    -- LOAD-BEARING
_ = refl

_ : seed fold ins₀ ≡ 1048576                           -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE MOVING SIDE.  Six drains of the SAME run, differing in fuel
-- alone.  Each is LOAD-BEARING and each could have failed in either
-- direction: a reading that stalled would say the accumulator is not
-- what deepens, and a reading that jumped would say the rate is not one
-- per arrival.  It is one per arrival, exactly, and the fuel is the
-- number of arrivals.
----------------------------------------------------------------------

_ : carried (drainAt 1 fold ins₀) ≡ 2                  -- LOAD-BEARING
_ = refl

_ : carried (drainAt 2 fold ins₀) ≡ 3                  -- LOAD-BEARING
_ = refl

_ : carried (drainAt 3 fold ins₀) ≡ 4                  -- LOAD-BEARING
_ = refl

_ : carried (drainAt 4 fold ins₀) ≡ 5                  -- LOAD-BEARING
_ = refl

_ : carried (drainAt 5 fold ins₀) ≡ 6                  -- LOAD-BEARING
_ = refl

_ : carried (drainAt 6 fold ins₀) ≡ 7                  -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE LEAF, INSTANTIATED AT THIS RUN.  It is green, and the rows above
-- are why: the fuel a row can afford is six and the seed is a million,
-- so nothing here has reached the crossing.  What the row buys is that
-- the growth is measured INSIDE the region the leaf quantifies over,
-- rather than at a triple chosen to break it.
----------------------------------------------------------------------

drF : Confirms (drain-dry-free 6 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry fold ins₀))) (proj₂ (proj₂ (entry fold ins₀))) Below)
drF = refl
