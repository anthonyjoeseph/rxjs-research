-- MANY DELIVERIES INSIDE ONE CASCADE — the region every sibling probe
-- here is silent about, and the one an entry seed cannot re-read its way
-- out of.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THIS REGION AND NOT ANOTHER.  The machine re-seeds the rank at
-- every arrival, so a run that grows one layer per arrival is paid for
-- however fast it grows — the sibling fuel rows establish exactly that
-- rate and nothing about any other.  What no re-seed reaches is growth
-- BETWEEN two seedings: one arrival, one entry triple, and a cascade
-- that goes on delivering synchronously underneath it.  That is the only
-- shape in which a run can outgrow the entry it was entered at, so it is
-- the only shape worth instantiating once the arrival re-seed has
-- landed.
--
-- HOW ONE ARRIVAL IS MADE TO DELIVER MANY TIMES.  The slot's synchronous
-- part is EMPTY and its tail carries a single value, so the subscribe
-- frame does nothing at all and the whole run happens under one arrival.
-- That value is mapped to a literal observable and flattened, so
-- subscribing the inner delivers its whole length inside the arrival's
-- own frame; the scan above re-wraps its accumulator once per delivery,
-- which is the one step known to deepen a reading along a run.  Fuel is
-- the instrument that makes the claim legible rather than a matter of
-- reading the emit stream: one unit of drain fuel is one arrival, so a
-- reading of three at fuel one is three layers no second entry paid for.
--
-- WHAT THE ROWS SAY.  The burst reads zero, so nothing is inherited from
-- the subscribe frame.  One unit of fuel takes the reading to the source
-- length, and a second unit moves it no further, which is what says the
-- growth was one cascade's and not a queue of arrivals being drained one
-- per unit.  The pair of programs then moves the source length: three
-- deliveries against six under one entry apiece, while the term gains
-- three symbols and the seed gains a factor of eight.  So the growth a
-- single entry has to dominate is LINEAR in a length the seed is
-- exponential in — the margin widens in the one parameter that moves
-- both sides, exactly as it does across arrivals.
--
-- WHAT IS NOT COVERED, and it is the honest boundary.  The cascade here
-- is one flattening layer deep and its inner is a literal, so the
-- deliveries are bounded by the term; nothing here reaches a cascade
-- whose inner is itself recursive, where the count would be the drain's
-- business rather than the source's.  The flattening axis is not swept
-- either — a merge only — since what is being asked is whether a cascade
-- can grow at all under one entry, not which registry clause carries it.
--
-- TARGET: drain-dry-free @400cf7
module Probed.Cascade-Growth where

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_; _^_; _⊔_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; InstEvent; value; InstEmit; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; sizeᵉ;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ; input)
open import Rx.Slots using (Slots; slotsSize; scripted)
open import Rx.Evaluator using (Stream; Sched; EvalSt; drain; subscribeE;
  rootWitness; root; sched-init; st-init)
open import Rx.Nest-Depth using (nestDᵉ)
open import Verify-Rank-Sufficient using (drain-dry-free)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- The quantities, taken verbatim from the sibling probes so that a row
-- here is comparable with a row there: how deep the values a run hands
-- out read, what the ROOT is seeded at, and the drain with its fuel left
-- as a parameter — which is the instrument this file turns on a single
-- arrival rather than on a queue of them.
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

burstOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
burstOf e ins = proj₁ (entry e ins)

drainAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
drainAt f e ins = drain f 1 (proj₁ (proj₂ (entry e ins))) (proj₂ (proj₂ (entry e ins)))

----------------------------------------------------------------------
-- THE SLOT.  Nothing synchronous and one late value: the subscribe frame
-- is empty by construction, so every layer any row below reads was grown
-- under the arrival's own entry and not inherited from the root's.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 0 , 9 ∷ []))

----------------------------------------------------------------------
-- THE PROGRAM.  The arriving value is mapped to a literal observable and
-- flattened, so one arrival subscribes one inner that delivers its whole
-- length synchronously; the scan re-wraps its accumulator once per
-- delivery.  The two versions differ in that length alone, which is the
-- axis that moves the cascade and the term together.
----------------------------------------------------------------------

step : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

burst3 : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burst3 = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))

burst6 : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burst6 = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ []))

casc3 : Closed Γ₁ (obs natᵗ)
casc3 = scanᵉ step (strmᵗ emptyᵉ) (mergeAllᵉ nothing (mapᵉ burst3 (input zero)))

casc6 : Closed Γ₁ (obs natᵗ)
casc6 = scanᵉ step (strmᵗ emptyᵉ) (mergeAllᵉ nothing (mapᵉ burst6 (input zero)))

----------------------------------------------------------------------
-- THE CASCADE OF THREE.  The first row is what makes the rest mean
-- anything: an empty burst, so the root's entry contributed no layer at
-- all.  The second is the finding — three layers at one unit of fuel —
-- and the third is what rules out the reading that would explain it away,
-- since a queue drained one arrival per unit would still be climbing at
-- fuel two.
----------------------------------------------------------------------

_ : carried (burstOf casc3 insLate) ≡ 0                -- LOAD-BEARING
_ = refl

_ : carried (drainAt 1 casc3 insLate) ≡ 3              -- LOAD-BEARING
_ = refl

_ : carried (drainAt 2 casc3 insLate) ≡ 3              -- LOAD-BEARING
_ = refl

_ : nestDᵉ casc3 ≡ 2                                   -- LOAD-BEARING
_ = refl

_ : seed casc3 insLate ≡ 1048576                       -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE CASCADE OF SIX — the growth row, and the only one a single program
-- could not have given.  Twice the deliveries under one entry apiece,
-- against a seed that has gained a factor of eight for the three extra
-- literals.  Linear against exponential in the same parameter.
----------------------------------------------------------------------

_ : carried (burstOf casc6 insLate) ≡ 0                -- LOAD-BEARING
_ = refl

_ : carried (drainAt 1 casc6 insLate) ≡ 6              -- LOAD-BEARING
_ = refl

_ : carried (drainAt 2 casc6 insLate) ≡ 6              -- LOAD-BEARING
_ = refl

_ : seed casc6 insLate ≡ 8388608                       -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE LEAF AT THE DEEPER OF THE PAIR.  The drain row is the half that
-- carries the cascade, and it is the one this file is really about.
----------------------------------------------------------------------

drC : Confirms (drain-dry-free 2 1 0
  (proj₁ (proj₂ (entry casc6 insLate))) (proj₂ (proj₂ (entry casc6 insLate))) Below)
drC = refl
