-- MANY DELIVERIES INSIDE ONE CASCADE — the region every sibling probe
-- here is silent about, and the one no per-arrival re-seeding reaches.
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

-- WHAT THE ROWS SAY.  The burst reads zero, so nothing is inherited from
-- the subscribe frame.  One unit of fuel takes the reading to the source
-- length, and a second unit moves it no further, which is what says the
-- growth was one cascade's and not a queue of arrivals being drained one
-- per unit.  The pair of programs then moves that length — three
-- deliveries against six under one entry apiece — while the term's own
-- hop reading does not move AT ALL, eighteen for both.  A longer literal
-- adds no flattener, so the axis that grows the cascade is one the
-- reading is blind to.
--
-- SO THE AXIS WAS PUSHED PAST THE READING, AND THAT IS THE FINDING.
-- Twenty-four literals hand out values reading twenty-four against a
-- term still reading eighteen, and the run is dry-free anyway.  A value
-- deeper than the program that produced it reads is therefore NOT the
-- crossing: the guard peels on a SUBSCRIBE, and an accumulator handed
-- out of the root is subscribed by nobody however deep it reads.  Which
-- retires the margin framing these rows were written under — the
-- quantity it compared was never the one the guard consults.
--
-- WHAT IS NOT COVERED, and it is the honest boundary.  The cascade here
-- is one flattening layer deep and its inner is a literal, so the
-- deliveries are bounded by the term; nothing here reaches a cascade
-- whose inner is itself recursive, where the count would be the drain's
-- business rather than the source's.  The flattening axis is not swept
-- either — a merge only — since what is being asked is whether a cascade
-- can grow at all under one entry, not which registry clause carries it.
-- Nor does any row here SUBSCRIBE a value it grew, which is where the
-- crossing now looks to be and where the next rows are owed.
--
-- TARGET: drain-dry-free @0b82eb
module Probed.Cascade-Growth where

open import Data.Fin using (Fin; zero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Bool using (false)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; InstEvent; value; InstEmit; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Stream; Sched; EvalSt; drain; subscribeE;
  rootWitness; root; sched-init; st-init; hasDry)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Rank-Sufficient using (drain-dry-free)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- The quantities, taken verbatim from the sibling probe so that a row
-- here is comparable with a row there: how deep the values a run hands
-- out read, in the currency the rank itself is denominated in, and the
-- drain with its fuel left as a parameter — which is the instrument this
-- file turns on a single arrival rather than on a queue of them.
----------------------------------------------------------------------

evHop : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) →
        List (InstEvent (Closed Γ u)) → ℕ
evHop V η []             = 0
evHop V η (value v ∷ es) = hopDᵉ V η v ⊔ evHop V η es
evHop V η (_ ∷ es)       = evHop V η es

carried : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) →
          Stream Γ (obs u) → ℕ
carried V η []         = 0
carried V η (em ∷ ems) = evHop V η (InstEmit.events em) ⊔ carried V η ems

-- THE STORE BOUND every reading here is taken at.  `evaluate` builds
-- its schedule at the fuel it then hands the drain, so a row is about a
-- RUN only when the two agree — and this is the fuel the drain row
-- below spends.  A row free to pick the bound separately would be
-- picking how tight the statement it instantiates is.
SB : ℕ
SB = 2

entry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Stream Γ t × Sched Γ × EvalSt e
entry e ins =
  subscribeE (rootWitness SB e ins) e root 0 0 (sched-init SB e ins) (st-init e)

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
-- delivery.  The three versions differ in that length alone, which is
-- the axis that moves the cascade while leaving the term's reading
-- where it was.
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
-- THE PAIR.  The burst rows are what make the rest mean anything: empty,
-- so the root's entry contributed no hop at all.  The drain rows at one
-- unit of fuel are the finding, and the rows at two are what rule out the
-- reading that would explain it away, since a queue drained one arrival
-- per unit would still be climbing at fuel two.  The two term readings
-- are the fixed side, and they are fixed at the same figure.
----------------------------------------------------------------------

η₁ : Fin 1 → ℕ
η₁ = slotHop SB insLate

_ : carried SB η₁ (burstOf casc3 insLate) ≡ 0          -- LOAD-BEARING
_ = refl

_ : carried SB η₁ (drainAt 1 casc3 insLate) ≡ 3        -- LOAD-BEARING
_ = refl

_ : carried SB η₁ (drainAt 2 casc3 insLate) ≡ 3        -- LOAD-BEARING
_ = refl

_ : hopDᵉ SB η₁ casc3 ≡ 18                             -- LOAD-BEARING
_ = refl

_ : carried SB η₁ (burstOf casc6 insLate) ≡ 0          -- LOAD-BEARING
_ = refl

_ : carried SB η₁ (drainAt 1 casc6 insLate) ≡ 6        -- LOAD-BEARING
_ = refl

_ : carried SB η₁ (drainAt 2 casc6 insLate) ≡ 6        -- LOAD-BEARING
_ = refl

_ : hopDᵉ SB η₁ casc6 ≡ 18                             -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- PAST THE TERM'S OWN READING.  The pair above moves the cascade without
-- moving the reading at all, so the axis can be pushed until the run
-- hands out values deeper than the program that produced them reads.
-- Twenty-four literals against a reading of eighteen is the first place
-- that is true.
----------------------------------------------------------------------

burst24 : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burst24 = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ nat̂ 7 ∷ nat̂ 8 ∷ nat̂ 9 ∷ nat̂ 10 ∷ nat̂ 11 ∷ nat̂ 12 ∷ nat̂ 13 ∷ nat̂ 14 ∷ nat̂ 15 ∷ nat̂ 16 ∷ nat̂ 17 ∷ nat̂ 18 ∷ nat̂ 19 ∷ nat̂ 20 ∷ nat̂ 21 ∷ nat̂ 22 ∷ nat̂ 23 ∷ nat̂ 24 ∷ []))

casc24 : Closed Γ₁ (obs natᵗ)
casc24 = scanᵉ step (strmᵗ emptyᵉ) (mergeAllᵉ nothing (mapᵉ burst24 (input zero)))

_ : hopDᵉ SB η₁ casc24 ≡ 18                            -- LOAD-BEARING
_ = refl

_ : carried SB η₁ (drainAt 1 casc24 insLate) ≡ 24      -- LOAD-BEARING
_ = refl

-- THE ROW THIS FILE IS NOW REALLY ABOUT.  The reading above is a third
-- past the term's own, and the run is still dry-free — so a value being
-- deeper than the program that produced it reads is NOT the crossing.
-- What the guard peels on is a SUBSCRIBE, and an accumulator handed out
-- of the root is subscribed by nobody, however deep it reads.
_ : hasDry (drainAt 1 casc24 insLate) ≡ false          -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE LEAF AT THE DEEPER OF THE PAIR.  The drain row is the half that
-- carries the cascade, and it is the one this file is really about.
----------------------------------------------------------------------

drC : Confirms (drain-dry-free SB 1
  (proj₁ (proj₂ (entry casc6 insLate))) (proj₂ (proj₂ (entry casc6 insLate))) Below)
drC = refl
