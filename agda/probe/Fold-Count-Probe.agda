------------------------------------------------------------------
-- THE FOLD-COUNT PROBE: does one cascade's fold count fit
-- `cWid * cReg * cSize`?
--
-- J-Budget-Probe settled the SHAPE of the count — `cWid * cReg` is
-- short by a chain-length factor, and `cWid * cReg * cSize` covers the
-- size and width blowups pM produces.  What it did NOT settle is the
-- count itself: it gated `iterSize`/`iterFold` at the new count against
-- a measured store, never the number of `frameStep` increments a
-- cascade actually spends.  That number is `j`, the receipt the
-- companion tree sums, and `cascadeGo-caps` asserts `j ≤ cWid * cReg *
-- cSize`.  This probe is that assertion's gate.
--
-- WHAT `j` IS, read off the ground clauses.  Every receipt in the
-- delivery clique is either 0 or a sum:
--
--     foldPath root          ↦ 0
--     foldPath (share-sink i)↦ dispatchShare's
--     foldPath (f ↠ p)       ↦ stepFrame's + the tail's
--     dispatchShare          ↦ shareGo's
--     shareGo []             ↦ 0
--     shareGo (cancelled ∷ ) ↦ the tail's
--     shareGo (live ∷ )      ↦ foldPath's + the tail's
--
-- so `j` is the TOTAL number of frame crossings in the cascade, summed
-- over every chain the cascade walks — breadth as well as depth,
-- because `shareGo` adds its siblings rather than maxing them.
--
-- THE INSTRUMENT: the evaluator's own `delivered` ledger.  `cascade`
-- resets it per arrival and every folding registration pushes its
-- `rid`, so after one cascade the list IS that cascade's fold sequence —
-- no instrumentation of `stepFrame` required.  Its length counts folds;
-- its length after deduplication counts the registrations involved.
--
-- WHAT IT FINDS, and it refutes the counting route rather than gating
-- it.  Nested shares make one cascade's delivery count EXPONENTIAL in
-- the number of shared slots while every `Caps` component stays linear
-- or constant:
--
--     shared levels k     0    1    2    3    4
--     deliveries          2    6   14   30   62      = 2 ^ (k+2) - 2
--     registrations       2    4    6    8   10      = 2k + 2
--     cSize, cWid              constant (6, 1)
--
-- Two consequences, in increasing order of damage:
--
--   (1) THE SNAPSHOT FACT IS FALSE.  "Each registration folds at most
--       once per cascade" — the ingredient the counting route was to be
--       built on — fails at ONE shared level: four ledger entries drawn
--       from three registrations (Measurement 3).  `shareGo` writes
--       `delivered` but never reads it, and a registration reachable by
--       two paths through the share DAG is dispatched down both.
--
--   (2) THE COUNT IS SHORT, not by a factor but by a class.  The folds
--       are real — the scan under the ladder folds 1, 2, 4, 8 times in
--       ONE cascade (Measurement 4) — so `j ≥ 2 ^ k` against a budget
--       `cWid * cReg * cSize = 12k + 6`, and 2 ^ k passes it at k = 7.
--
-- The escape itself is past what this normalises (k = 7 is 128 folds of
-- a growing store), so the crossover is stated as arithmetic over the
-- measured laws rather than as one `refl` at the crossing depth.
------------------------------------------------------------------
module Fold-Count-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_; _⊔_) renaming (_≡ᵇ_ to _≡ᵇⁿ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; sum; map; length; foldr; any)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fsuc)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; after_,_; hot; InstEmit; InstEvent;
                           value; init; close; handoff; complete)
open import Rx.Exp  using (Ctx; Closed; Tm; Fn; Ty; natᵗ; obs; _×ᵗ_; input;
                           ofᵉ; mergeAllᵉ; mapᵉ; scanᵉ; strmᵗ; nat̂; sndᵗ;
                           fstᵗ; varᵗ; sizeᵉ; sizeᵛ; sizeᵗ)
open import Rx.Evaluator using (Slots; Slot; scripted; shared; Sched; EvalSt;
                                LiveSource; NodeState; scan-st; take-st;
                                merge-st; concat-st; switch-st; exhaust-st;
                                sched-init; sched-next; st-init; budgetAt;
                                subscribeE; cascade; slotsSize; root; Stream;
                                Arrival; Path; share-sink; _↠_;
                                Frame; map-f; scan-f; take-f;
                                from-inner; thru-outer)
open import Rx.Frame-Width using (outWᵉ; outWᵛ)
open import Verify-Budget-Sufficient using (Caps; caps; capsOK?; iterSize;
                                            iterFold; foldStep; frameStep)

------------------------------------------------------------------
-- THE HARNESS, keeping the NEXT ID as well as the state, so one more
-- cascade can be run at the right instant and its burst inspected
------------------------------------------------------------------

drainSt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Fuel → Id → Sched Γ → EvalSt e → Id × Sched Γ × EvalSt e
drainSt zero    nextId sched st = nextId , sched , st
drainSt (suc k) nextId sched st with sched-next sched
... | inj₁ _            = nextId , sched , st
... | inj₂ (a , sched′) =
      let (_ , sched″ , st′) = cascade a nextId sched′ st
      in drainSt k (suc nextId) sched″ st′

runSt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
      → Id × Sched Γ × EvalSt e
runSt fuel e ins =
  let (_ , sched₀ , st₀) =
        subscribeE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
  in drainSt fuel 1 sched₀ st₀

stAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
     → Sched Γ × EvalSt e
stAt fuel e ins = proj₂ (runSt fuel e ins)

-- THE CASCADE UNDER THE MICROSCOPE: drain `fuel` arrivals, then run ONE
-- more and hand back its burst.  This is the exact cascade
-- `cascadeGo-caps` is stated about
burstAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
        → Stream Γ t
burstAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = []
...   | inj₂ (a , sched′) = proj₁ (cascade a nid sched′ st)

------------------------------------------------------------------
-- the quantities: `capsOK?`'s three, the chain length it now also
-- reads, and the two the burst exposes
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

pathLen : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathLen root           = 0
pathLen (share-sink i) = 0
pathLen (f ↠ p)        = suc (pathLen p)

mSize : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mSize fuel e ins =
  let (sched , st) = stAt fuel e ins
  in foldr (λ kv m → nodeSize (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)
     ⊔ foldr (λ l m → liveSize l ⊔ m) 0 (Sched.live sched)

mWid : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mWid {n = n} fuel e ins =
  let (sched , st) = stAt fuel e ins
  in foldr (λ kv m → nodeWid n (Sched.slots sched) (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)
     ⊔ foldr (λ l m → liveWid n (Sched.slots sched) l ⊔ m) 0 (Sched.live sched)

mReg : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mReg fuel e ins = length (EvalSt.registry (proj₂ (stAt fuel e ins)))

mChain : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mChain fuel e ins =
  foldr (λ en m → pathSize (proj₂ (proj₂ (proj₂ en))) ⊔ m) 0
        (EvalSt.registry (proj₂ (stAt fuel e ins)))

mLen : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mLen fuel e ins =
  foldr (λ en m → pathLen (proj₂ (proj₂ (proj₂ en))) ⊔ m) 0
        (EvalSt.registry (proj₂ (stAt fuel e ins)))

-- the tightest cSize admissible at a state: stored values, the chains'
-- step functions, AND (the round-4 repair) the chains' LENGTH
mS : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mS fuel e ins = mSize fuel e ins ⊔ mChain fuel e ins ⊔ mLen fuel e ins

-- THE BUDGET, at the tightest cap the pre-state admits
mBudget : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mBudget fuel e ins = mWid fuel e ins * mReg fuel e ins * mS fuel e ins

------------------------------------------------------------------
-- what the burst exposes: one emit per chain that reached a sink
------------------------------------------------------------------

evVals : ∀ {A : Set} → List (InstEvent A) → ℕ
evVals []               = 0
evVals (value _ ∷ es)   = suc (evVals es)
evVals (init _ ∷ es)    = evVals es
evVals (close _ _ ∷ es) = evVals es
evVals (handoff _ ∷ es) = evVals es
evVals (complete ∷ es)  = evVals es

-- the number of `foldPath`-to-sink calls in the cascade
mEmits : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mEmits fuel e ins = length (burstAt fuel e ins)

------------------------------------------------------------------
-- THE LEDGER ITSELF, which is the sharpest instrument here.  `cascade`
-- resets `delivered` per arrival and every folding registration pushes
-- its `rid`, so after one cascade the list IS that cascade's fold
-- sequence.  Its LENGTH is the number of folds; its length after
-- deduplication is the number of registrations involved.  The two are
-- equal exactly when each registration folded at most once
------------------------------------------------------------------

postAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → EvalSt e
postAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = st
...   | inj₂ (a , sched′) = proj₂ (proj₂ (cascade a nid sched′ st))

nub : List ℕ → List ℕ
nub []       = []
nub (x ∷ xs) = if any (_≡ᵇⁿ x) xs then nub xs else x ∷ nub xs

-- folds in the cascade
mFolds : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mFolds fuel e ins = length (EvalSt.delivered (postAt fuel e ins))

-- registrations that folded at least once
mFolders : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mFolders fuel e ins = length (nub (EvalSt.delivered (postAt fuel e ins)))

-- and the payloads they carried
mVals : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mVals fuel e ins =
  sum (map (λ em → evVals (InstEmit.events em)) (burstAt fuel e ins))

------------------------------------------------------------------
-- FAMILY A — J-Budget-Probe's pM, the chain-length family, re-measured
-- for its FOLD COUNT rather than its store
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

ins1 : Slots Γ₁
ins1 fz = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

v0 : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] (obs natᵗ ∷ Θ) (obs natᵗ)
v0 = varᵗ (here refl)

dup3 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ) (obs natᵗ)
dup3 = strmᵗ (mergeAllᵉ (ofᵉ (v0 ∷ v0 ∷ v0 ∷ [])))

liftN : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] natᵗ (obs natᵗ)
liftN = strmᵗ (ofᵉ (nat̂ 1 ∷ []))

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
-- FAMILY B — State-Blowup-Probe's registry families and deepScan
------------------------------------------------------------------

accV : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

-- the deepening scan: one fold towers the accumulator
wrap2ᵍ : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] ((obs natᵗ ×ᵗ natᵗ) ∷ Θ) (obs natᵗ)
wrap2ᵍ = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

deepScan : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepScan = strmᵗ (mergeAllᵉ (scanᵉ wrap2ᵍ seedO (mergeAllᵉ (ofᵉ (accV ∷ [])))))

pD : Closed Γ₁ natᵗ
pD = mergeAllᵉ (scanᵉ deepScan seedO (input fz))

-- the registry families: a scan whose step re-subscribes the INPUT, so
-- every fold mints a fresh registration
wrapIn : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapIn = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ strmᵗ (input fz) ∷ [])))

pR : Closed Γ₁ natᵗ
pR = mergeAllᵉ (scanᵉ wrapIn seedO (input fz))

src3 : ∀ {n} {Γ : Ctx n} → Closed Γ natᵗ
src3 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

pRs : Closed Γ₁ natᵗ
pRs = mergeAllᵉ (scanᵉ wrapIn seedO src3)

-- two live sources, the accumulator referencing both
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

ins2 : Slots Γ₂
ins2 fz        = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))
ins2 (fsuc fz) = scripted (hot ((after 0 , 4) ∷ (after 0 , 5) ∷ []))

wrapIn2 : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapIn2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ strmᵗ (input fz)
                                     ∷ strmᵗ (input (fsuc fz)) ∷ [])))

pR2 : Closed Γ₂ natᵗ
pR2 = mergeAllᵉ (scanᵉ wrapIn2 seedO (input fz))

------------------------------------------------------------------
-- FAMILY C — THE ADVERSARIAL ONE, and the reason this probe exists.
--
-- Families A and B all carry cReg ≤ 1 at their pre-states and have no
-- share fan-out at all, so none of them can stress the COUNT: their
-- cascades walk one chain.  The count's exposure is the delivery TREE,
-- and the tree branches at `share-sink`, where `dispatchShare` fans one
-- arrival out to every registration on the slot.
--
-- `dup` below subscribes its argument TWICE, so a shared slot under it
-- carries two registrations and one arrival delivers twice.  Stack the
-- shares — slot m's def is `dup (input (m+1))` — and delivery counts
-- double per level while the registry grows by two per level:
--
--     deliveries  2 ^ k        registrations  2 * k
--
-- If that is what the evaluator does, `j` is exponential in k against a
-- polynomial `cWid * cReg * cSize`, and the count is refuted — not the
-- theorem, but this shape of it: `shareGo` would have to report the MAX
-- of its siblings' receipts rather than their SUM.
------------------------------------------------------------------

dup : ∀ {n} {Γ : Ctx n} → Closed Γ natᵗ → Closed Γ natᵗ
dup e = mergeAllᵉ (ofᵉ (strmᵗ e ∷ strmᵗ e ∷ []))

-- ONE shared level
Γˢ¹ : Ctx 2
Γˢ¹ = natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insˢ¹ : Slots Γˢ¹
insˢ¹ fz        = shared (dup (input (fsuc fz)))
insˢ¹ (fsuc fz) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

pS1 : Closed Γˢ¹ natᵗ
pS1 = dup (input fz)

-- TWO shared levels
Γˢ² : Ctx 3
Γˢ² = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insˢ² : Slots Γˢ²
insˢ² fz               = shared (dup (input (fsuc fz)))
insˢ² (fsuc fz)        = shared (dup (input (fsuc (fsuc fz))))
insˢ² (fsuc (fsuc fz)) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

pS2 : Closed Γˢ² natᵗ
pS2 = dup (input fz)

-- THREE shared levels
Γˢ³ : Ctx 4
Γˢ³ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insˢ³ : Slots Γˢ³
insˢ³ fz                      = shared (dup (input (fsuc fz)))
insˢ³ (fsuc fz)               = shared (dup (input (fsuc (fsuc fz))))
insˢ³ (fsuc (fsuc fz))        = shared (dup (input (fsuc (fsuc (fsuc fz)))))
insˢ³ (fsuc (fsuc (fsuc fz))) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

pS3 : Closed Γˢ³ natᵗ
pS3 = dup (input fz)

------------------------------------------------------------------
-- FAMILY D — THE LADDER WITH A SCAN AT THE BOTTOM, and the sharpest
-- question this probe can ask.
--
-- Family C establishes that DELIVERIES per cascade double per shared
-- level.  On its own that refutes nothing: a value delivered to 2^k
-- places is still one value, and `capsOK?` reads sizes, not counts.
--
-- Put a SCAN under the ladder and the count becomes a size.  Every
-- delivery is one fold, every fold multiplies the stored accumulator by
-- the step function's occurrence count, so 2^k deliveries in ONE cascade
-- tower the store to 3 ^ (2 ^ k) while `cWid * cReg * cSize` grows
-- linearly in k.  If that is what runs, round 4's recurrence is short —
-- not the companion tree's bookkeeping, the recurrence itself.
------------------------------------------------------------------

-- THREE occurrences: every fold triples the store, so the size reads
-- the fold count EXPONENTIALLY and the terms stop normalising past
-- k = 2.  Kept because it is the shape that threatens the recurrence
wrap3 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap3 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ accV ∷ [])))

pF1 : Closed Γˢ¹ natᵗ
pF1 = mergeAllᵉ (scanᵉ wrap3 seedO (input fz))

pF2 : Closed Γˢ² natᵗ
pF2 = mergeAllᵉ (scanᵉ wrap3 seedO (input fz))

-- and the no-share control: the same scan over a plain scripted input,
-- so the ladder's contribution is the difference
pF0 : Closed Γ₁ natᵗ
pF0 = mergeAllᵉ (scanᵉ wrap3 seedO (input fz))

-- ONE occurrence: every fold adds a FIXED amount, so the stored size is
-- affine in the fold count and the ladder stays normalisable deeper.
-- This is the counter the deep measurements use
wrap1 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap1 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ [])))

pC0 : Closed Γ₁ natᵗ
pC0 = mergeAllᵉ (scanᵉ wrap1 seedO (input fz))

pC1 : Closed Γˢ¹ natᵗ
pC1 = mergeAllᵉ (scanᵉ wrap1 seedO (input fz))

pC2 : Closed Γˢ² natᵗ
pC2 = mergeAllᵉ (scanᵉ wrap1 seedO (input fz))

pC3 : Closed Γˢ³ natᵗ
pC3 = mergeAllᵉ (scanᵉ wrap1 seedO (input fz))

-- FOUR shared levels, to carry the doubling law past the point where
-- the registry count is left behind
Γˢ⁴ : Ctx 5
Γˢ⁴ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insˢ⁴ : Slots Γˢ⁴
insˢ⁴ fz                             = shared (dup (input (fsuc fz)))
insˢ⁴ (fsuc fz)                      = shared (dup (input (fsuc (fsuc fz))))
insˢ⁴ (fsuc (fsuc fz))               = shared (dup (input (fsuc (fsuc (fsuc fz)))))
insˢ⁴ (fsuc (fsuc (fsuc fz)))        = shared (dup (input (fsuc (fsuc (fsuc (fsuc fz))))))
insˢ⁴ (fsuc (fsuc (fsuc (fsuc fz)))) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

pC4 : Closed Γˢ⁴ natᵗ
pC4 = mergeAllᵉ (scanᵉ wrap1 seedO (input fz))

pS4 : Closed Γˢ⁴ natᵗ
pS4 = dup (input fz)

------------------------------------------------------------------
-- MEASUREMENT 1: THE TRIPLE IS LINEAR OR CONSTANT IN THE LADDER DEPTH.
--
-- At the pre-state — after the root subscribe, before the first cascade
-- — cSize and cWid do not move at all and cReg grows by two per shared
-- level.  Every quantity `capsOK?` reads is polynomial in k
------------------------------------------------------------------

_ : mS 0 pC1 insˢ¹ ≡ 6
_ = refl

_ : mS 0 pC2 insˢ² ≡ 6
_ = refl

_ : mS 0 pC3 insˢ³ ≡ 6
_ = refl

_ : mWid 0 pC1 insˢ¹ ≡ 1
_ = refl

_ : mWid 0 pC2 insˢ² ≡ 1
_ = refl

_ : mReg 0 pC1 insˢ¹ ≡ 3
_ = refl

_ : mReg 0 pC2 insˢ² ≡ 5
_ = refl

_ : mReg 0 pC3 insˢ³ ≡ 7
_ = refl

_ : mReg 0 pC4 insˢ⁴ ≡ 9
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 2: ONE CASCADE'S DELIVERY COUNT IS NOT.
--
-- `cascade` resets the `delivered` ledger per arrival and every folding
-- registration pushes its `rid`, so the ledger's LENGTH is the number of
-- `foldPath` deliveries in that cascade.  It doubles per shared level:
-- 2 ^ (k + 2) - 2 against a registry of 2k + 2
------------------------------------------------------------------

_ : mFolds 0 pS1 insˢ¹ ≡ 6
_ = refl

_ : mFolds 0 pS2 insˢ² ≡ 14
_ = refl

_ : mFolds 0 pS3 insˢ³ ≡ 30
_ = refl

_ : mFolds 0 pS4 insˢ⁴ ≡ 62
_ = refl

_ : mReg 0 pS4 insˢ⁴ ≡ 10
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 3: A REGISTRATION FOLDS MORE THAN ONCE PER CASCADE, and
-- this is the whole refutation of the counting route.
--
-- The route's key ingredient is the snapshot fact — each registration
-- folds at most once per cascade, off the `delivered` ledger — which
-- would bound one cascade's deliveries by `cReg`.  It is FALSE at a
-- single shared level: the ledger holds four entries drawn from three
-- registrations.  `shareGo` records `rid` in `delivered` but never
-- CONSULTS it, and a registration reachable by two paths through the
-- share DAG is dispatched down both
------------------------------------------------------------------

_ : mFolds 0 pC1 insˢ¹ ≡ 4
_ = refl

_ : mFolders 0 pC1 insˢ¹ ≡ 3
_ = refl

-- and the gap widens: at two levels each registration folds twice over
_ : mFolds 0 pC2 insˢ² ≡ 10
_ = refl

_ : mFolders 0 pC2 insˢ² ≡ 5
_ = refl

_ : mFolds 0 pC3 insˢ³ ≡ 22
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 4: THE DELIVERIES ARE REAL FOLDS, not bookkeeping.
--
-- `wrap1` adds a fixed amount to the stored accumulator per fold, so
-- the stored size is affine in the fold count — `3 + 7 * folds`.  Read
-- backwards, the scan under the ladder folds 1, 2, 4, 8 times in ONE
-- cascade as the ladder goes 0, 1, 2, 3 levels deep.  Each of those
-- crosses the `scan-f` frame, which is the clause `stepFrame-caps`
-- charges a `j` for, so `j ≥ 2 ^ k`
------------------------------------------------------------------

_ : mSize 1 pC0 ins1 ≡ 10
_ = refl

_ : mSize 1 pC1 insˢ¹ ≡ 17
_ = refl

_ : mSize 1 pC2 insˢ² ≡ 31
_ = refl

_ : mSize 1 pC3 insˢ³ ≡ 59
_ = refl

-- with a TRIPLING step function the same fold counts tower the store,
-- so the growth per fold is multiplicative and not merely additive
_ : mSize 1 pF0 ins1 ≡ 24
_ = refl

_ : mSize 1 pF1 insˢ¹ ≡ 87
_ = refl

_ : mSize 1 pF2 insˢ² ≡ 843
_ = refl

------------------------------------------------------------------
-- THE CONSEQUENCE, in arithmetic.  The tight admissible cap at the
-- family's pre-state is `caps 6 1 (2k+1)`, so
--
--     budget  =  cWid * cReg * cSize  =  1 * (2k+1) * 6  =  12k + 6
--     folds   =  2 ^ k
--
-- and the second passes the first for good at k = 7 — 128 against 90.
-- Below is the crossover, stated at the two depths that bracket it, and
-- the two depths this probe can normalise, where the budget still wins
------------------------------------------------------------------

_ : ((2 * 2 * 2) ≤ᵇ 12 * 3 + 6) ≡ true    -- k = 3:   8 ≤ 42
_ = refl

_ : ((2 * 2 * 2 * 2 * 2 * 2) ≤ᵇ 12 * 6 + 6) ≡ true   -- k = 6:  64 ≤ 78
_ = refl

_ : ((2 * 2 * 2 * 2 * 2 * 2 * 2) ≤ᵇ 12 * 7 + 6) ≡ false  -- k = 7: 128 > 90
_ = refl
