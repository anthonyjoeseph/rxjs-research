------------------------------------------------------------------
-- THE MINT-LOOP PROBE: does the minting feedback loop CLOSE?
--
-- Fold-Count-Probe derived `j ≤ 2 ^ cReg * cSize` and gated it over four
-- share shapes.  One spot in that derivation is crude, and it is flagged
-- at the `frameBlowup` site: `shareAdmit` reads the registry AS OF THE
-- DISPATCH, not a snapshot taken at cascade entry, so a fold that MINTS a
-- registration on a shared slot widens the branching for every later
-- dispatch of that slot.  The honest recursion is
--
--     deliveries d ≤ 2 ^ R_end       R_end ≤ R₀ + d * (mints per delivery)
--
-- which has no closed bound on its face — substitute the second into the
-- first and the right side outruns the left forever.  Fold-Count-Probe's
-- family G sampled ONE rung of that loop (mint once, deliver to the
-- minted) and found four orders of magnitude of slack.  deepScan is the
-- standing lesson about what one rung of a tower is worth: it always
-- looks absorbable.
--
-- SO THIS PROBE CLOSES THE LOOP.  `mintG′ (suc k)` re-subscribes the
-- shared slot THROUGH A SCAN whose own step mints at level k, so a minted
-- chain can itself mint and branching feeds branching inside one cascade.
-- Nothing exotic: it is a scan under a share whose step function's
-- emitted observable subscribes that share, nested k deep.
--
-- THE FINDING: THE LOOP DOES NOT TOWER, and the count stands.
--
--   (1) DELIVERIES SATURATE IN THE NESTING DEPTH.  Three ladders, k = 0 …:
--
--         L = 1    5   5   5
--         L = 2   20  26  27  27
--         L = 3   50 106 176 232 260 268 269      (lean variant)
--
--       Nesting buys deliveries and then stops buying them.  The reason
--       is structural: a rung only widens branching by MINTING, a minted
--       registration is only reachable by dispatches that come AFTER it,
--       and the number of dispatches still to come is fixed by the
--       PRE-STATE DAG.  Once the nesting is deeper than the pre-state's
--       remaining dispatch rounds, the extra levels are never reached.
--
--   (2) THE ENTRY REGISTRY DOES NOT MOVE WITH k — 3, 5, 7 for the three
--       ladders, every k.  The nested scans are subscribed mid-cascade
--       and never at the root subscribe, which is exactly why they looked
--       dangerous: they are free at the pre-state the budget is read off.
--
--   (3) BUT THE ENTRY cSize DOES, LINEARLY: each nesting level adds a
--       constant to the step function's syntax, so cSize climbs 3, 10,
--       18, 26, 34, 42, 50 while the deliveries flatten.  The budget
--       `2 ^ cReg * cSize` therefore GROWS in k while the count
--       SATURATES, and the ratio is worst at k = 0 — the plain
--       non-nested mint, which family G already gated.
--
--       Worst ratio anywhere in the sweep, and it falls with ladder
--       depth rather than climbing:  L = 2, k = 0 → 16/96 = 0.17;
--       L = 3, k = 0 → 50/384 = 0.13; accumulating L = 3 → 106/1024 = 0.10.
--
-- THE FEEDBACK IS REAL rxjs, not an evaluator artifact, and that had to
-- be checked because it is what decides whether the loop exists at all.
-- In rxjs 7.8:
--
--     const src = new Subject();
--     const s = merge(src, src).pipe(share());   // one arrival, two emissions
--     let armed = true;
--     s.subscribe(v => { log('A' + v);
--       if (armed) { armed = false; s.subscribe(w => log('B' + w)); } });
--     src.next(1);                               // ⇒  A1 A1 B1
--
-- A subscriber added mid-cascade misses the IN-FLIGHT emission and
-- receives the cascade's LATER ones — which is precisely the evaluator's
-- behaviour, and precisely what makes a mid-cascade mint able to widen
-- the same cascade.
--
-- WHAT IS MEASURED HOW.  The pre-state caps (`mReg`, `mS` at fuel 0) are
-- cheap: they need only the root subscribe.  The fold counts are not —
-- every one re-runs the evaluator through a real cascade.  The counts are
-- therefore pinned by `refl` and the gate is then arithmetic over the
-- pinned numbers, the same economy Fold-Count-Probe's crossover uses.
--
-- ONE RUNG IS MISSING AND IT IS NAMED: the ACCUMULATING three-level
-- ladder at k = 1 (`mFolds 0 (pG′³ 1) insG³`) does not normalise here —
-- 46 minutes and 7.2 GB without an answer.  Its k-sweep is carried by the
-- LEAN variant, which drops the `accV` occurrence from the step so the
-- accumulator stays a fixed term while every registration, dispatch and
-- delivery is unchanged.  The lean and accumulating families are not the
-- same program (the lean one delivers less: 16 vs 20 at L = 2, k = 0),
-- so the lean sweep is evidence about the SHAPE of the k-dependence, and
-- the accumulating family is gated wherever it does normalise.
------------------------------------------------------------------
module Mint-Loop-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _≤ᵇ_; _⊔_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; sum; map; length; foldr)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fsuc)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; after_,_; hot)
open import Rx.Exp  using (Ctx; Closed; Exp; Tm; natᵗ; obs; _×ᵗ_; input;
                           ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; nat̂;
                           fstᵗ; varᵗ; sizeᵉ; sizeᵛ; sizeᵗ)
open import Rx.Evaluator using (Slots; scripted; shared; Sched; EvalSt;
                                LiveSource; NodeState; scan-st; take-st;
                                merge-st; concat-st; switch-st; exhaust-st;
                                sched-init; sched-next; st-init; budgetAt;
                                subscribeE; cascade; root; Path;
                                share-sink; _↠_;
                                Frame; map-f; scan-f; take-f;
                                from-inner; thru-outer)

------------------------------------------------------------------
-- THE HARNESS, Fold-Count-Probe's, kept to the parts this file reads
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

nodeSize : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeSize (scan-st {t} v)   = sizeᵛ t v
nodeSize (concat-st q _ _) = sum (map sizeᵉ q)
nodeSize (take-st _)       = 0
nodeSize (merge-st _ _)    = 0
nodeSize (switch-st _ _)   = 0
nodeSize (exhaust-st _ _)  = 0

liveSize : ∀ {n} {Γ : Ctx n} → LiveSource Γ → ℕ
liveSize l = foldr (λ tv m → sizeᵛ (LiveSource.elemTy l) (proj₂ tv) ⊔ m) 0
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

-- the tightest cSize the state admits
mS : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mS fuel e ins = mSize fuel e ins ⊔ mChain fuel e ins ⊔ mLen fuel e ins

postAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → EvalSt e
postAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = st
...   | inj₂ (a , sched′) = proj₂ (proj₂ (cascade a nid sched′ st))

-- one cascade's deliveries, off the evaluator's own reset-per-arrival ledger
mFolds : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mFolds fuel e ins = length (EvalSt.delivered (postAt fuel e ins))

------------------------------------------------------------------
-- THE SHAPES
------------------------------------------------------------------

accV : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

seedO : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] Θ (obs natᵗ)
seedO = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

dup : ∀ {n} {Γ : Ctx n} {Θ} → Exp Γ [] [] Θ natᵗ → Exp Γ [] [] Θ natᵗ
dup e = mergeAllᵉ (ofᵉ (strmᵗ e ∷ strmᵗ e ∷ []))

------------------------------------------------------------------
-- ONE SHARED LEVEL.  Five scripted emissions rather than two, because a
-- mid-emission subscriber misses the in-flight emission: the feedback is
-- one instant behind, so it can only be watched over several instants
------------------------------------------------------------------

Γˢ¹ : Ctx 2
Γˢ¹ = natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insG : Slots Γˢ¹
insG fz        = shared (dup (input (fsuc fz)))
insG (fsuc fz) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ (after 0 , 3)
                                 ∷ (after 0 , 4) ∷ (after 0 , 5) ∷ []))

mintG′ : ∀ {Θ} → ℕ → Tm Γˢ¹ [] [] Θ (obs natᵗ)
mintG′ zero    = strmᵗ (input fz)
mintG′ (suc k) =
  strmᵗ (mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′ k ∷ []))))
                          seedO (input fz)))

pG′ : ℕ → Closed Γˢ¹ natᵗ
pG′ k = mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′ k ∷ []))))
                         seedO (input fz))

------------------------------------------------------------------
-- TWO SHARED LEVELS, so share-DAG branching and self-similar minting
-- compound
------------------------------------------------------------------

Γˢ² : Ctx 3
Γˢ² = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insG² : Slots Γˢ²
insG² fz               = shared (dup (input (fsuc fz)))
insG² (fsuc fz)        = shared (dup (input (fsuc (fsuc fz))))
insG² (fsuc (fsuc fz)) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ (after 0 , 3)
                                         ∷ (after 0 , 4) ∷ (after 0 , 5) ∷ []))

mintG′² : ∀ {Θ} → ℕ → Tm Γˢ² [] [] Θ (obs natᵗ)
mintG′² zero    = strmᵗ (input fz)
mintG′² (suc k) =
  strmᵗ (mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′² k ∷ []))))
                          seedO (input fz)))

pG′² : ℕ → Closed Γˢ² natᵗ
pG′² k = mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′² k ∷ []))))
                          seedO (input fz))

------------------------------------------------------------------
-- THREE SHARED LEVELS.  The escape risk that is left after the nesting
-- direction saturates is the LADDER direction, so the tower is run over
-- the deepest ladder this normalises on
------------------------------------------------------------------

Γˢ³ : Ctx 4
Γˢ³ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insG³ : Slots Γˢ³
insG³ fz                      = shared (dup (input (fsuc fz)))
insG³ (fsuc fz)               = shared (dup (input (fsuc (fsuc fz))))
insG³ (fsuc (fsuc fz))        = shared (dup (input (fsuc (fsuc (fsuc fz)))))
insG³ (fsuc (fsuc (fsuc fz))) = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

mintG′³ : ∀ {Θ} → ℕ → Tm Γˢ³ [] [] Θ (obs natᵗ)
mintG′³ zero    = strmᵗ (input fz)
mintG′³ (suc k) =
  strmᵗ (mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′³ k ∷ []))))
                          seedO (input fz)))

pG′³ : ℕ → Closed Γˢ³ natᵗ
pG′³ k = mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ mintG′³ k ∷ []))))
                          seedO (input fz))

-- THE LEAN VARIANT, which carries the k-sweep the accumulating one
-- cannot reach.  Dropping `accV` from the step leaves the accumulator a
-- fixed term while every registration, dispatch and delivery keeps its
-- shape — less delivery, same k-dependence
mintOnly² : ∀ {Θ} → ℕ → Tm Γˢ² [] [] Θ (obs natᵗ)
mintOnly² zero    = strmᵗ (input fz)
mintOnly² (suc k) = strmᵗ (mergeAllᵉ (scanᵉ (mintOnly² k) seedO (input fz)))

pL² : ℕ → Closed Γˢ² natᵗ
pL² k = mergeAllᵉ (scanᵉ (mintOnly² k) seedO (input fz))

mintOnly³ : ∀ {Θ} → ℕ → Tm Γˢ³ [] [] Θ (obs natᵗ)
mintOnly³ zero    = strmᵗ (input fz)
mintOnly³ (suc k) = strmᵗ (mergeAllᵉ (scanᵉ (mintOnly³ k) seedO (input fz)))

pL³ : ℕ → Closed Γˢ³ natᵗ
pL³ k = mergeAllᵉ (scanᵉ (mintOnly³ k) seedO (input fz))

------------------------------------------------------------------
-- MEASUREMENT 1: THE ENTRY REGISTRY IS INVARIANT IN THE NESTING DEPTH.
--
-- This is the fact that makes the family adversarial at all.  The nested
-- scans live inside a step function, so they are subscribed mid-cascade
-- and never at the root subscribe: they are FREE at the pre-state the
-- budget is read off.  If deliveries towered in k, the budget's
-- exponential would be reading a number that does not move
------------------------------------------------------------------

_ : mReg 0 (pG′ 0) insG ≡ 3
_ = refl

_ : mReg 0 (pG′ 2) insG ≡ 3
_ = refl

_ : mReg 0 (pG′² 0) insG² ≡ 5
_ = refl

_ : mReg 0 (pG′² 3) insG² ≡ 5
_ = refl

_ : mReg 0 (pL³ 0) insG³ ≡ 7
_ = refl

_ : mReg 0 (pL³ 6) insG³ ≡ 7
_ = refl

_ : mReg 0 (pG′³ 0) insG³ ≡ 7
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 2: BUT THE ENTRY cSize IS LINEAR IN IT.
--
-- Each nesting level adds a constant to the step function's syntax, and
-- the step function is a `scan-f` frame on a registered chain, so
-- `pathSize` reads it.  cSize climbs by 8 (lean) or 14 (accumulating)
-- per level and never stops.  This is the budget's answer to the nesting:
-- `2 ^ cReg * cSize` grows in k even though `cReg` does not
------------------------------------------------------------------

_ : mS 0 (pL³ 0) insG³ ≡ 3
_ = refl

_ : mS 0 (pL³ 1) insG³ ≡ 10
_ = refl

_ : mS 0 (pL³ 2) insG³ ≡ 18
_ = refl

_ : mS 0 (pL³ 3) insG³ ≡ 26
_ = refl

_ : mS 0 (pL³ 4) insG³ ≡ 34
_ = refl

_ : mS 0 (pL³ 5) insG³ ≡ 42
_ = refl

_ : mS 0 (pL³ 6) insG³ ≡ 50
_ = refl

_ : mS 0 (pG′² 0) insG² ≡ 8
_ = refl

_ : mS 0 (pG′² 1) insG² ≡ 22
_ = refl

_ : mS 0 (pG′² 2) insG² ≡ 36
_ = refl

_ : mS 0 (pG′² 3) insG² ≡ 50
_ = refl

_ : mS 0 (pG′³ 0) insG³ ≡ 8
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 3: THE DELIVERIES SATURATE.
--
-- The whole question, in three rows.  Deeper nesting buys deliveries and
-- then stops buying them — 5 flat at one level, 27 at two, 269 at three.
-- A rung can only widen branching by MINTING; a minted registration is
-- reachable only by dispatches that come AFTER it; and how many
-- dispatches are still to come is fixed by the PRE-STATE DAG.  Past that
-- depth the extra levels are never reached at all
------------------------------------------------------------------

-- one shared level: flat from the start
_ : mFolds 0 (pG′ 0) insG ≡ 5
_ = refl

_ : mFolds 0 (pG′ 1) insG ≡ 5
_ = refl

_ : mFolds 0 (pG′ 2) insG ≡ 5
_ = refl

-- two shared levels: rises, then stops
_ : mFolds 0 (pG′² 0) insG² ≡ 20
_ = refl

_ : mFolds 0 (pG′² 1) insG² ≡ 26
_ = refl

_ : mFolds 0 (pG′² 2) insG² ≡ 27
_ = refl

_ : mFolds 0 (pG′² 3) insG² ≡ 27
_ = refl

-- two shared levels, lean: the same shape at smaller numbers
_ : mFolds 0 (pL² 0) insG² ≡ 16
_ = refl

_ : mFolds 0 (pL² 2) insG² ≡ 21
_ = refl

_ : mFolds 0 (pL² 4) insG² ≡ 21
_ = refl

-- three shared levels: the longest climb, and it still flattens
_ : mFolds 0 (pL³ 0) insG³ ≡ 50
_ = refl

_ : mFolds 0 (pL³ 1) insG³ ≡ 106
_ = refl

_ : mFolds 0 (pL³ 2) insG³ ≡ 176
_ = refl

_ : mFolds 0 (pL³ 3) insG³ ≡ 232
_ = refl

_ : mFolds 0 (pL³ 4) insG³ ≡ 260
_ = refl

_ : mFolds 0 (pL³ 5) insG³ ≡ 268
_ = refl

_ : mFolds 0 (pL³ 6) insG³ ≡ 269
_ = refl

-- and the accumulating three-level ladder at the one rung it reaches,
-- which is the tightest single point in the file: 106 deliveries against
-- a pre-state registry of 7
_ : mFolds 0 (pG′³ 0) insG³ ≡ 106
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 4: ACROSS INSTANTS, where the mints of one cascade are the
-- registry of the next.  This is the direction the recursion actually
-- runs, and it is self-limiting for the same reason: every extra
-- delivery costs a REGISTRATION, and a registration doubles the budget.
-- Deliveries grow additively in what minting adds; the budget grows
-- multiplicatively in it
--
--     k  instant   folds   cReg   cSize
--     0     0        5       3      8
--     0     1       13       6     21
--     0     2       29      13     39
--     2     0        5       3     36
--     2     1       20       7     77
--     2     2      114      35    151
--
-- The last row is measured the same way as the rest but is NOT in the
-- refl wall below: it is a 114-delivery cascade over a 35-registration
-- registry and costs more than the other thirty assertions together.
-- Nothing rests on it — it is the row that shows the trend continuing,
-- and the trend is already `refl`-checked twice above it
------------------------------------------------------------------

_ : mFolds 1 (pG′ 0) insG ≡ 13
_ = refl

_ : mReg 1 (pG′ 0) insG ≡ 6
_ = refl

_ : mS 1 (pG′ 0) insG ≡ 21
_ = refl

_ : mFolds 2 (pG′ 0) insG ≡ 29
_ = refl

_ : mReg 2 (pG′ 0) insG ≡ 13
_ = refl

_ : mFolds 1 (pG′ 2) insG ≡ 20
_ = refl

_ : mReg 1 (pG′ 2) insG ≡ 7
_ = refl

_ : mS 1 (pG′ 2) insG ≡ 77
_ = refl

------------------------------------------------------------------
-- THE GATE.  Every row above against `2 ^ cReg * cSize` at the tightest
-- caps the pre-state admits.  Arithmetic over the pinned numbers rather
-- than a re-run of the evaluator per assertion — the counts are already
-- `refl`-checked above, and re-deriving each one inside a `≤ᵇ` would
-- triple an already long probe.
--
-- Read the ratios down the k-column and the finding is there: the budget
-- pulls AWAY from the count as the nesting deepens, because the count
-- flattens and the budget does not
------------------------------------------------------------------

-- one shared level, k = 0, 1, 2:  5 against 2 ^ 3 * 8
_ : (5 ≤ᵇ 2 ^ 3 * 8) ≡ true
_ = refl

-- two shared levels, k = 0 … 3:  20, 26, 27, 27 against 2 ^ 5 * {8,22,36,50}
_ : (20 ≤ᵇ 2 ^ 5 * 8) ≡ true
_ = refl

_ : (26 ≤ᵇ 2 ^ 5 * 22) ≡ true
_ = refl

_ : (27 ≤ᵇ 2 ^ 5 * 36) ≡ true
_ = refl

_ : (27 ≤ᵇ 2 ^ 5 * 50) ≡ true
_ = refl

-- three shared levels, lean, k = 0 … 6 against 2 ^ 7 * {3,10,18,26,34,42,50}
_ : (50 ≤ᵇ 2 ^ 7 * 3) ≡ true
_ = refl

_ : (106 ≤ᵇ 2 ^ 7 * 10) ≡ true
_ = refl

_ : (176 ≤ᵇ 2 ^ 7 * 18) ≡ true
_ = refl

_ : (232 ≤ᵇ 2 ^ 7 * 26) ≡ true
_ = refl

_ : (260 ≤ᵇ 2 ^ 7 * 34) ≡ true
_ = refl

_ : (268 ≤ᵇ 2 ^ 7 * 42) ≡ true
_ = refl

_ : (269 ≤ᵇ 2 ^ 7 * 50) ≡ true
_ = refl

-- the accumulating three-level ladder, the tightest point measured
_ : (106 ≤ᵇ 2 ^ 7 * 8) ≡ true
_ = refl

-- and across instants: 13 at (6, 21), 20 at (7, 77)
_ : (13 ≤ᵇ 2 ^ 6 * 21) ≡ true
_ = refl

_ : (20 ≤ᵇ 2 ^ 7 * 77) ≡ true
_ = refl

------------------------------------------------------------------
-- THE WORST RATIO IN THE FILE, and it is at k = 0 — the NON-nested mint,
-- the shape family G already gated.  Nesting is not the escape direction;
-- it is the direction the budget wins in.  Nor is ladder depth: the ratio
-- at k = 0 FALLS from two levels to three
--
--     L = 2, k = 0    16 / (2 ^ 5 *  3)  =  0.17
--     L = 3, k = 0    50 / (2 ^ 7 *  3)  =  0.13
--     L = 3, k = 0    106 / (2 ^ 7 * 8)  =  0.10   (accumulating)
--
-- stated as the comparison that a growing ratio would break: three times
-- the lean L = 3, k = 0 count still fits its budget, and would not have
-- if the ratio had climbed by the ladder step rather than fallen
------------------------------------------------------------------

_ : (16 * 2 ≤ᵇ 2 ^ 5 * 3) ≡ true
_ = refl

_ : (50 * 2 ≤ᵇ 2 ^ 7 * 3) ≡ true
_ = refl

_ : (106 * 9 ≤ᵇ 2 ^ 7 * 8) ≡ true
_ = refl
