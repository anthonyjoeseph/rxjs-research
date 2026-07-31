------------------------------------------------------------------
-- THE J-BUDGET PROBE: `cWid * cReg` IS NOT ENOUGH ITERATIONS, and no
-- count computed from the Caps triple ever will be.
--
-- Round 4's recurrence is `Caps (suc id) = frameBlowup (Caps id)` with
-- `frameBlowup c = frameStep (cWid c * cReg c) c`.  State-Blowup-Probe
-- gated the SHAPE of one step — `foldStep`, `sizeStep`, and the additive
-- registration rule — but never the COUNT.  The count is what the
-- induction's last joint consumes: `caps-tick` sums the `j′` receipts
-- `subscribeE-caps` hands back and must fit the total under it.
--
-- WHY IT WAS SUSPECT.  A fold is not the only size-growing event
-- `capsOK?` can see.  A payload crossing a `map-f` frame is substituted
-- into that frame's step function — the same `size-subΘᵉ` shape a fold
-- has — and the grown value lands in whatever the chain ends in.  So one
-- cascade's events look like
--
--     emissions  ×  chains  ×  CHAIN LENGTH
--
-- and `cWid * cReg` has a factor for the first and the second and none
-- for the third.
--
-- WHAT IT FINDS, and it is stronger than "short by a path factor": `pM k`
-- below is a family whose pre-state caps are CONSTANT in k — cSize 7,
-- cWid 1, cReg 1 for every k ≥ 1 — while one cascade's stored result runs
-- 15, 51, 159, 483, unbounded in k.  The only quantity that moves is the
-- chain length, 3 ↦ 7, and `capsOK?` does not bound it.  So no count
-- `f cSize cWid cReg` can suffice: the triple cannot tell `pM 1` from
-- `pM 4`.  `tickFits-absurd` is the machine-checked instance.
--
-- THE FIX THIS FORCES, and it stays inside the round-5 gate
-- (`frameBlowup : Caps → Caps` — no ledger, no receipt, no E):
-- `pathSz?` must bound a chain's LENGTH by cSize, not only each frame's
-- step function.  It already walks the chain; the missing conjunct is
-- `pathLen p ≤ᵇ B`, and Measurement 3 shows it is fixed per chain and
-- untouched by cascades, so a per-instant recurrence can carry it.  It
-- reads nothing outside `Caps`, so round3b-ledger-reset-absurd stays
-- unavailable, exactly as it does for round 4's own components.
--
-- AND THE COUNT THIS PROBE PROPOSED IS ITSELF REFUTED — read
-- Fold-Count-Probe before building on anything below.  This file used
-- to conclude `cWid * cReg * cSize`, one factor per dimension of
-- "emissions × chains × chain length".  Two things are wrong with it,
-- and neither is visible from any family here:
--
--   · THE COUNT IS SHORT BY A CLASS.  Every program in this file walks
--     ONE chain per cascade, so none of them can stress the count's
--     middle factor.  Nested shares make one cascade's deliveries
--     exponential in the shared-slot count while the whole triple stays
--     linear — 2 ^ (k+2) - 2 deliveries against 2k + 2 registrations —
--     and `2 ^ k` passes `12k + 6` for good at k = 7.
--   · THE cWid FACTOR WAS NEVER A FACTOR OF THIS COUNT.  cWid bounds
--     how WIDE one emitted observable is, not how many times a cascade
--     iterates.  The 1 ↦ 81 measured below is a per-fold blowup, and the
--     per-fold `foldStep` / `sizeStep` gates in State-Blowup-Probe are
--     what answer it.
--
-- The replacement, derived from the share DAG and gated there, is
-- `2 ^ cReg * cSize`: a DAG on cReg registrations carries at most
-- `2 ^ cReg - 1` delivery paths, and each path crosses at most cSize
-- frames — which is the conjunct (i) above supplies.  So this probe's
-- surviving contribution is the chain-length conjunct, not the product.
------------------------------------------------------------------
module J-Budget-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _≤ᵇ_; _⊔_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; sum; map; length; foldr)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fsuc)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; after_,_; hot)
open import Rx.Exp  using (Ctx; Closed; Tm; Fn; Ty; natᵗ; obs; _×ᵗ_; input;
                           ofᵉ; mergeAllᵉ; mapᵉ; scanᵉ; strmᵗ; nat̂; sndᵗ; varᵗ;
                           sizeᵉ; sizeᵛ; sizeᵗ)
open import Rx.Evaluator using (Slots; scripted; Sched; EvalSt; LiveSource;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                sched-init; sched-next; st-init; budgetAt;
                                subscribeE; cascade; slotsSize; root;
                                Path; share-sink; _↠_;
                                Frame; map-f; scan-f; take-f;
                                from-inner; thru-outer)
open import Rx.Frame-Width using (outWᵉ; outWᵛ)
open import Verify-Budget-Sufficient using (Caps; caps; capsOK?; iterSize;
                                            iterFold; foldStep; frameStep)

------------------------------------------------------------------
-- THE HARNESS: the evaluator's own drain loop, keeping the state
-- instead of the emit stream (identical to State-Blowup-Probe's)
------------------------------------------------------------------

drainSt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Fuel → Id → Sched Γ → EvalSt e → Sched Γ × EvalSt e
drainSt zero    _      sched st = sched , st
drainSt (suc k) nextId sched st with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
      let (_ , sched″ , st′) = cascade a nextId sched′ st
      in drainSt k (suc nextId) sched″ st′

runSt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
      → Sched Γ × EvalSt e
runSt fuel e ins =
  let (_ , sched₀ , st₀) =
        subscribeE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
  in drainSt fuel 1 sched₀ st₀

------------------------------------------------------------------
-- the quantities capsOK? reads, plus the one it does NOT: chain LENGTH
------------------------------------------------------------------

nodeSize : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeSize (scan-st {t} v)   = sizeᵛ t v
nodeSize (concat-st q _ _) = sum (map sizeᵉ q)
nodeSize (take-st _)       = 0
nodeSize (merge-st _ _)    = 0
nodeSize (switch-st _ _)   = 0
nodeSize (exhaust-st _ _)  = 0

nodeWid : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → NodeState Γ → ℕ
nodeWid j sl (scan-st {t} v)   = outWᵛ j sl t v
nodeWid j sl (concat-st q _ _) = foldr (λ o m → outWᵉ j sl o ⊔ m) 0 q
nodeWid j sl (take-st _)       = 0
nodeWid j sl (merge-st _ _)    = 0
nodeWid j sl (switch-st _ _)   = 0
nodeWid j sl (exhaust-st _ _)  = 0

liveSize : ∀ {n} {Γ : Ctx n} → LiveSource Γ → ℕ
liveSize l = foldr (λ tv m → sizeᵛ (LiveSource.elemTy l) (proj₂ tv) ⊔ m) 0
                   (LiveSource.pending l)

liveWid : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → LiveSource Γ → ℕ
liveWid j sl l = foldr (λ tv m → outWᵛ j sl (LiveSource.elemTy l) (proj₂ tv) ⊔ m) 0
                       (LiveSource.pending l)

-- `pathSz?`'s quantity: the largest step function sitting in a chain,
-- which is what `sizeStep`'s multiplier S reads
frameSize : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → ℕ
frameSize (map-f fn)         = sizeᵗ fn
frameSize (scan-f fn _)      = sizeᵗ fn
frameSize (take-f _)         = 0
frameSize (from-inner _ _ _) = 0
frameSize (thru-outer _ _)   = 0

pathSize : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathSize root           = 0
pathSize (share-sink i) = 0
pathSize (f ↠ p)        = frameSize f ⊔ pathSize p

-- and the quantity NOTHING in `Caps` bounds: how MANY frames
pathLen : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathLen root           = 0
pathLen (share-sink i) = 0
pathLen (f ↠ p)        = suc (pathLen p)

mSize : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mSize fuel e ins =
  let (sched , st) = runSt fuel e ins
  in foldr (λ kv m → nodeSize (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)
     ⊔ foldr (λ l m → liveSize l ⊔ m) 0 (Sched.live sched)

mWid : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mWid {n = n} fuel e ins =
  let (sched , st) = runSt fuel e ins
  in foldr (λ kv m → nodeWid n (Sched.slots sched) (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)
     ⊔ foldr (λ l m → liveWid n (Sched.slots sched) l ⊔ m) 0 (Sched.live sched)

mReg : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mReg fuel e ins = length (EvalSt.registry (proj₂ (runSt fuel e ins)))

mChain : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mChain fuel e ins =
  foldr (λ en m → pathSize (proj₂ (proj₂ (proj₂ en))) ⊔ m) 0
        (EvalSt.registry (proj₂ (runSt fuel e ins)))

mLen : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mLen fuel e ins =
  foldr (λ en m → pathLen (proj₂ (proj₂ (proj₂ en))) ⊔ m) 0
        (EvalSt.registry (proj₂ (runSt fuel e ins)))

-- the TIGHTEST cSize that satisfies capsOK?'s size conjuncts at a
-- state: stored values AND the chains' step functions
mCap : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mCap fuel e ins = mSize fuel e ins ⊔ mChain fuel e ins

------------------------------------------------------------------
-- THE PROGRAM FAMILY: a map chain of length k, every frame TRIPLING
-- its payload, ending in a scan that stores what arrives.
--
-- The point of the family is that k moves the CHAIN LENGTH while
-- leaving every `Caps` quantity at the pre-state fixed: the stored
-- accumulator is the seed, the registry holds one entry, and each
-- frame's step function is the same `dup3`.  So if the budget is a
-- function of the triple alone, one k must escape it.
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

ins1 : Slots Γ₁
ins1 fz = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

-- the payload variable at obs natᵗ
v0 : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] (obs natᵗ ∷ Θ) (obs natᵗ)
v0 = varᵗ (here refl)

-- THREE occurrences of the payload: one crossing triples the size
dup3 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ) (obs natᵗ)
dup3 = strmᵗ (mergeAllᵉ (ofᵉ (v0 ∷ v0 ∷ v0 ∷ [])))

-- lift the scripted nat arrival into an observable payload
liftN : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] natᵗ (obs natᵗ)
liftN = strmᵗ (ofᵉ (nat̂ 1 ∷ []))

-- the scan STORES what arrives, so the chain's growth is visible to
-- `capsOK?` rather than escaping to the sink
keep : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ obs natᵗ) (obs natᵗ)
keep = sndᵗ (varᵗ (here refl))

seedO : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] Θ (obs natᵗ)
seedO = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

mapChain : ℕ → Closed Γ₁ (obs natᵗ)
mapChain zero    = mapᵉ liftN (input fz)
mapChain (suc k) = mapᵉ dup3 (mapChain k)

pM : ℕ → Closed Γ₁ natᵗ
pM k = mergeAllᵉ (scanᵉ keep seedO (mapChain k))

------------------------------------------------------------------
-- MEASUREMENT 1: THE TRIPLE IS CONSTANT IN k.
--
-- At the pre-state — after the root subscribe, before the first
-- cascade — every quantity `capsOK?` reads is the same for every k ≥ 1.
-- cSize is 7 because the largest thing in the state is one `dup3`; cWid
-- is 1 because the stored accumulator is the seed; cReg is 1 because the
-- one scripted input carries one registration
------------------------------------------------------------------

_ : mCap 0 (pM 1) ins1 ≡ 7
_ = refl

_ : mCap 0 (pM 4) ins1 ≡ 7
_ = refl

_ : mWid 0 (pM 1) ins1 ≡ 1
_ = refl

_ : mWid 0 (pM 4) ins1 ≡ 1
_ = refl

_ : mReg 0 (pM 1) ins1 ≡ 1
_ = refl

_ : mReg 0 (pM 4) ins1 ≡ 1
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 2: ONE CASCADE'S RESULT IS NOT.
--
-- The stored accumulator after a single cascade — one arrival crossing k
-- tripling `map-f` frames and one fold.  s ↦ 3s + 6, exactly dup3's
-- three occurrences, once per frame.  Unbounded in k against a fixed
-- triple.  (The sequence continues 1455, 4371, … ; it is cut at k = 4
-- because every gate here re-runs the evaluator and the point is made.)
------------------------------------------------------------------

_ : mSize 1 (pM 0) ins1 ≡ 3
_ = refl

_ : mSize 1 (pM 1) ins1 ≡ 15
_ = refl

_ : mSize 1 (pM 2) ins1 ≡ 51
_ = refl

_ : mSize 1 (pM 3) ins1 ≡ 159
_ = refl

_ : mSize 1 (pM 4) ins1 ≡ 483
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 3: WHAT DOES MOVE — the chain length, k + 3 (the k map
-- frames, the scan frame, mergeAll's thru-outer, and the root).
--
-- This is the whole content of the refutation: the one quantity that
-- separates these programs is the one `capsOK?` was blind to
------------------------------------------------------------------

_ : mLen 0 (pM 0) ins1 ≡ 3
_ = refl

_ : mLen 0 (pM 1) ins1 ≡ 4
_ = refl

_ : mLen 0 (pM 4) ins1 ≡ 7
_ = refl

-- and it does NOT grow per instant: this chain is built once, by the
-- root subscribe, and the cascades leave its length alone.  So the
-- missing conjunct is one a per-instant recurrence can carry
_ : mLen 1 (pM 4) ins1 ≡ 7
_ = refl

-- it only ever SHRINKS: the scripted source is spent after its second
-- arrival and cascadeFinish drops its entries, emptying the registry
_ : mLen 2 (pM 4) ins1 ≡ 0
_ = refl

------------------------------------------------------------------
-- THE REFUTATION.  `frameStep (cWid c * cReg c) c` does not cover one
-- cascade from a state satisfying `capsOK? c`.
--
-- Stated over `runSt`, uniform in the program, at a concrete `c` — one
-- instance is all a ∀-statement needs.  `caps 7 1 1` is admissible at pM
-- 4's pre-state (the 7 is both the largest term AND the chain length, so
-- the statement survives the length conjunct the fix adds), and its
-- count is 1 * 1 = 1: one `sizeStep`, taking 7 to 7 * 15 = 105, against
-- a measured 483
------------------------------------------------------------------

TickFitsAt : Caps → Set
TickFitsAt c = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  capsOK? c (proj₁ (runSt 0 e ins)) (proj₂ (runSt 0 e ins)) ≡ true →
  capsOK? (frameStep (Caps.cWid c * Caps.cReg c) c)
          (proj₁ (runSt 1 e ins)) (proj₂ (runSt 1 e ins)) ≡ true

-- the pre-state is inside the cap
_ : capsOK? (caps 7 1 1) (proj₁ (runSt 0 (pM 4) ins1))
                         (proj₂ (runSt 0 (pM 4) ins1)) ≡ true
_ = refl

-- and one cascade escapes the old count
_ : capsOK? (frameStep 1 (caps 7 1 1)) (proj₁ (runSt 1 (pM 4) ins1))
                                       (proj₂ (runSt 1 (pM 4) ins1)) ≡ false
_ = refl

tickFits-absurd : TickFitsAt (caps 7 1 1) → ⊥
tickFits-absurd tf with tf (pM 4) ins1 refl
... | ()

-- the arithmetic behind it, written out: one sizeStep from 7 is 105
_ : iterSize 7 1 7 ≡ 105
_ = refl

_ : (483 ≤ᵇ 105) ≡ false
_ = refl

------------------------------------------------------------------
-- AND WHY NO OTHER COUNT OF THE TRIPLE WOULD DO.  The refutation above
-- is at one `c`, but the family makes the general claim: pM 1 … pM 4 all
-- present the SAME (cSize, cWid, cReg) = (7, 1, 1) at their pre-states
-- (Measurement 1) while their cascades store 15 … 483 (Measurement 2).
-- A count `f cSize cWid cReg` returns one number for all of them, and
-- `iterSize 7 (f 7 1 1) 7` is one number too, so some k passes it.
--
-- The escape is therefore not a bigger count — it is that cSize must SEE
-- the chain length.  Measurement 3 says what that costs: a conjunct on a
-- quantity `pathSz?` already walks past, fixed per chain, untouched by
-- the cascades
------------------------------------------------------------------

-- what the length conjunct demands of the base cap, on the family:
-- chain length is under the entry measure with room to spare
_ : (mLen 0 (pM 4) ins1 ≤ᵇ 2 + sizeᵉ (pM 4) + slotsSize ins1) ≡ true
_ = refl

-- and it is NOT implied by the size conjuncts: at k = 4 the two are
-- equal at 7, and one more map frame separates them for good
_ : (mLen 0 (pM 4) ins1 ≤ᵇ mCap 0 (pM 4) ins1) ≡ true
_ = refl

------------------------------------------------------------------
-- THE GATE FOR THE REPLACEMENT COUNT, `cWid * cReg * cSize`.
--
-- The tightest admissible cap at pM 4's pre-state is `caps 7 1 1`, so
-- the new count is 1 * 1 * 7 = 7 and the size dimension has seven
-- `sizeStep`s to spend where it had one.  Only cSize is gated end to
-- end: `iterFold` composes to a tower and does not normalise
-- (State-Blowup-Probe says why), so the width dimension is gated one
-- fold at a time, as it is there
------------------------------------------------------------------

_ : (mSize 1 (pM 4) ins1 ≤ᵇ iterSize 7 (1 * 1 * 7) 7) ≡ true
_ = refl

-- two of the seven already cover it, so the count is not tight — which
-- is the point: it has to dominate a chain it cannot see the end of
_ : (mSize 1 (pM 4) ins1 ≤ᵇ iterSize 7 2 7) ≡ true
_ = refl

-- THE WIDTH DIMENSION SHOWS THE SAME DEFECT, which is worth stating
-- separately: the stored width goes 1 ↦ 81, one tripling per map frame,
-- so it too is unbounded in k against a fixed triple.  ONE `foldStep` at
-- this cap allows 49 — so the old count is short in the width dimension
-- as well, not only the size one
_ : mWid 1 (pM 4) ins1 ≡ 81
_ = refl

_ : (mWid 1 (pM 4) ins1 ≤ᵇ foldStep 7 1) ≡ false
_ = refl

-- two of the new count's seven folds cover it with room to spare
_ : (mWid 1 (pM 4) ins1 ≤ᵇ iterFold 7 2 1) ≡ true
_ = refl

-- registrations: this family never grows the registry, so the cReg
-- dimension is slack throughout
_ : mReg 1 (pM 4) ins1 ≡ 1
_ = refl

_ : (mReg 1 (pM 4) ins1 ≤ᵇ 1 * suc (7 * 7)) ≡ true
_ = refl
