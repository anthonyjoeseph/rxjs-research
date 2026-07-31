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
-- TWO NUMBERS, AND THEY ARE NOT THE SAME NUMBER.  `D`, the DELIVERIES,
-- is one per registration the cascade folds into.  `j`, the conjunct's
-- own index, is one per FRAME STEPPED — what `foldPath-caps` accumulates
-- at its `↠` clause, and a delivery whose path is `root` or `share-sink`
-- costs none.  This file measured only D when it was written and read the
-- result as a statement about j.  MEASUREMENT 5 now counts j directly and
-- the two answers differ in kind, not just in scale, so both are below
-- and each is used for what it settles.
--
-- THE FINDING: THE LOOP DOES NOT TOWER — but the ROUTE to the count is
-- dead and the count itself has to change.  In detail:
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
--       18, 26, 34, 42, 50.
--
--   (4) `D ≤ 2 ^ cReg` IS FALSE, and that is the derivation's own
--       intermediate step.  L = 3 lean, k = 2: 176 deliveries against an
--       entry registry of 7, and 2 ^ 7 = 128.  The DAG-path count is over
--       R_end, and the mint puts R_end above cReg — which is exactly what
--       the crude spot said and what this probe was run to price.  It is
--       priced, and the price is not zero: the intermediate claim is
--       refuted, so `D * cSize ≤ 2 ^ cReg * cSize` is unavailable, and
--       with it the whole "paths × frames-per-path" route.
--
--       What survives is the same injection with a SECOND COORDINATE:
--       deliveries into (subset of the pre-state registry) × (an index)
--       rather than into subsets alone.
--
--   (5) AND THE SPLIT INTO TWO COORDINATES IS DEAD, both ways it was
--       tried.  MEASUREMENT 6 gives the coordinates definitions and
--       measures them: the fibre of a pre-state class is 4 against a
--       cSize of 3 on the lean two-level ladder, so `≤ cSize` is out; it
--       then ATTAINS `2 ^ cReg` exactly (128 against 128) on the
--       three-level one, and MEASUREMENT 7 runs a fourth ladder where it
--       reaches 576 against a cap of 512, so `≤ 2 ^ cReg` is out too.
--       The ratio runs 0.25, 0.41, 1.00, 1.13 and is still climbing, so
--       no constant multiple of `2 ^ cReg` is safe either.
--
--       The FIRST coordinate is exactly what the story said — mPre is
--       4, 10, 22, 46 for entry registries of 3, 5, 7, 9, about
--       `2 ^ (cReg / 2)`, and invariant in k because the pre-state
--       classes are fixed by the pre-state DAG.  Which is precisely why
--       the split does not decompose anything: D is (something small)
--       times (something the size of D).
--
--   (6) SO THE DELIVERY BOUND IS STATED WHOLE: `D ≤ 2 ^ cReg * 2 ^ cReg`,
--       gated on every row here with the margin GROWING as the ladder
--       deepens (0.078, 0.026, 0.016, 0.0097).  The count is
--       `2 ^ cReg * 2 ^ cReg * cSize`.
--
--   (7) j DOES NOT FALL MONOTONICALLY IN k, which the D-only reading of
--       this file claimed.  L = 3 lean, j against the intermediate
--       `2 ^ cReg * cSize`:
--
--         k        0     1     2     3     4     5     6
--         j       58   226   548   912  1164  1268  1291
--         ratio  .15   .18   .24   .27   .27   .24   .20
--
--       It PEAKS at k = 3 and only then falls — j keeps climbing after D
--       has flattened, because the nesting lengthens the chains even once
--       it stops widening them.  The peak is interior, so "deeper is
--       safer" was the wrong lesson; the right one is that both j and D
--       saturate while cSize does not.
--
--       Worst ratio anywhere in the file, against the OLD count:
--       accumulating L = 3, k = 0 — 324 / (2 ^ 7 * 8) = 0.32, at k = 0
--       again, the plain non-nested mint family G already gated.
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

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _≤ᵇ_; _≡ᵇ_; _⊔_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; sum; map; length; foldr; any)
open import Data.Vec  using (lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fsuc)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; Tick; Gas; after_,_; hot)
open import Rx.Exp  using (Ctx; Closed; Exp; Tm; Val; natᵗ; obs; _×ᵗ_; input;
                           ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; nat̂;
                           fstᵗ; varᵗ; sizeᵉ; sizeᵛ; sizeᵗ)
open import Rx.Evaluator using (Slots; scripted; shared; Sched; EvalSt;
                                LiveSource; NodeState; scan-st; take-st;
                                merge-st; concat-st; switch-st; exhaust-st;
                                sched-init; sched-next; st-init; budgetAt;
                                subscribeE; cascade; root; Path;
                                share-sink; _↠_;
                                Frame; map-f; scan-f; take-f;
                                from-inner; thru-outer;
                                RegId; Arrival; arrTy; arrVal; arrTick;
                                stepFrame; shareAdmit; shareLatch; shareFinish;
                                chainsOf; cascadeLatch)

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
-- `j` ITSELF, which is NOT the delivery count.  Everything above this
-- line measures DELIVERIES, and the conjunct bounds FRAMES: `j` is what
-- `foldPath-caps` accumulates, one summand per `↠` clause, and a
-- delivery whose path is `root` or `share-sink` costs zero of them.
-- The two were conflated when this file was written, and the difference
-- decides the derivation (see THE ROUTE IS DEAD, below), so the frames
-- get counted directly.
--
-- The mirror is `foldPath` / `dispatchShare` / `shareGo` / `cascadeGo`
-- clause for clause with the emit stream deleted and a ℕ threaded in its
-- place; it calls the REAL `stepFrame`, `shareAdmit`, `shareLatch` and
-- `shareFinish`, so the state it walks is the state the evaluator walks.
-- `mJ-faithful` checks that by comparing its final delivery ledger with
-- `mFolds`, which comes off the evaluator proper.
--
-- IT IS A LOWER BOUND on the conjunct's `j`, not the value: this counts
-- ONE per frame, and `stepFrame-caps` may report more than one when a
-- frame re-enters `subscribeE` (from-inner / thru-outer).  So a row that
-- BREAKS the budget here breaks it for real; a row that fits is evidence
-- and not a proof
------------------------------------------------------------------

-- a DELIVERY DESCRIPTOR: the registrations on the path from the root
-- chain down to this delivery, deepest first.  This is the object the
-- injection at `cascadeGo-deliveries` sends somewhere, made concrete, so
-- that `preClasses` and `fibreCap` stop being opaque and start being
-- measurable
Desc : Set
Desc = List RegId

fpFolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
        → Gas → ℕ → Id → Tick → Desc → Path Γ u t → List (Val Γ u) → Bool
        → Sched Γ → EvalSt e → ℕ × List Desc × Sched Γ × EvalSt e

dsFolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Gas → ℕ → Id → Tick → Desc → (i : Fin n)
        → List (Val Γ (lookup Γ i)) → Bool
        → Sched Γ → EvalSt e → ℕ × List Desc × Sched Γ × EvalSt e

sgFolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Gas → ℕ → Id → Tick → Desc → (i : Fin n)
        → List (Val Γ (lookup Γ i)) → Bool
        → List (RegId × Path Γ (lookup Γ i) t)
        → Sched Γ → EvalSt e → ℕ × List Desc × Sched Γ × EvalSt e

fpFolds sf gas id now acc root vals fin sched st = 0 , [] , sched , st
fpFolds sf gas id now acc (share-sink i) vals fin sched st =
  dsFolds sf gas id now acc i vals fin sched st
fpFolds sf gas id now acc (f ↠ p) vals fin sched st =
  let (vals′ , _ , fin′ , sched₁ , st₁) = stepFrame sf id now f p vals fin sched st
      (m , ds , sched₂ , st₂) = fpFolds sf gas id now acc p vals′ fin′ sched₁ st₁
  in suc m , ds , sched₂ , st₂

dsFolds sf zero id now acc i vals fin sched st = 0 , [] , sched , st
dsFolds sf (suc gas) id now acc i vals fin sched st =
  let (m , ds , sched₁ , st₁) =
        sgFolds sf gas id now acc i vals fin
          (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)
      (_ , sched₂ , st₂) = shareFinish i fin ([] , sched₁ , st₁)
  in m , ds , sched₂ , st₂

sgFolds sf gas id now acc i vals fin []               sched st = 0 , [] , sched , st
sgFolds sf gas id now acc i vals fin ((rid , p) ∷ ps) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = sgFolds sf gas id now acc i vals fin ps sched st
... | false =
  let d = rid ∷ acc
      (m₁ , ds₁ , sched₁ , st₁) =
        fpFolds sf gas id now d p vals fin sched
                (record st { delivered = rid ∷ EvalSt.delivered st })
      (m₂ , ds₂ , sched₂ , st₂) = sgFolds sf gas id now acc i vals fin ps sched₁ st₁
  in m₁ + m₂ , d ∷ (ds₁ ++ ds₂) , sched₂ , st₂

csFolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → (a : Arrival Γ) → Id → List (RegId × Path Γ (arrTy a) t)
        → Sched Γ → EvalSt e → ℕ × List Desc × Sched Γ × EvalSt e
csFolds a id []                   sched st = 0 , [] , sched , st
csFolds {n = n} {e = e} a id ((rid , c) ∷ chains) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = csFolds a id chains sched st
... | false =
  let d = rid ∷ []
      (m₁ , ds₁ , sched₁ , st₁) =
        fpFolds (budgetAt e (Sched.slots sched) id) n id (arrTick a) d c
                (arrVal a ∷ []) (Arrival.isLast a) sched
                (record st { delivered = rid ∷ EvalSt.delivered st })
      (m₂ , ds₂ , sched₂ , st₂) = csFolds a id chains sched₁ st₁
  in m₁ + m₂ , d ∷ (ds₁ ++ ds₂) , sched₂ , st₂

-- the run: the frames, the descriptors, the post-state, and the RegIds
-- the ENTRY registry held — the pre-state the first coordinate reads
jAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
    → ℕ × List Desc × EvalSt e × List RegId
jAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = 0 , [] , st , []
...   | inj₂ (a , sched′) =
        let (m , ds , _ , st′) = csFolds a nid (chainsOf a st) sched′ (cascadeLatch a st)
        in m , ds , st′ , map proj₁ (EvalSt.registry st)

-- the frames one cascade steps
mJ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mJ fuel e ins = proj₁ (jAt fuel e ins)

-- the same walk's delivery ledger, for the faithfulness check
mJdel : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mJdel fuel e ins = length (EvalSt.delivered (proj₁ (proj₂ (proj₂ (jAt fuel e ins)))))

-- and the descriptor count, which must agree with it: one descriptor per
-- delivery is the whole point
mJdesc : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mJdesc fuel e ins = length (proj₁ (proj₂ (jAt fuel e ins)))

------------------------------------------------------------------
-- THE TWO COORDINATES, DEFINED.  `cascadeGo-deliveries` postulates the
-- injection `delivery ↦ (pre-state class, index)` and bounds the two
-- coordinates separately at `preClasses-bound` and `fibreCap-bound`.
-- Both coordinates are opaque FUNCTIONS in the assembly, which means the
-- split locates work without proving anything — so here they are given
-- definitions and measured, which is the cheapest way to find out
-- whether `fibreCap ≤ cSize` is even true before anyone proves it.
--
-- The class of a delivery is the sub-list of its descriptor lying in the
-- ENTRY registry; the fibre of a class is how many deliveries share it
------------------------------------------------------------------

memN : ℕ → List ℕ → Bool
memN x xs = any (_≡ᵇ x) xs

bfilter : (ℕ → Bool) → List ℕ → List ℕ
bfilter p []       = []
bfilter p (x ∷ xs) = if p x then x ∷ bfilter p xs else bfilter p xs

eqNL : List ℕ → List ℕ → Bool
eqNL []       []       = true
eqNL []       (_ ∷ _)  = false
eqNL (_ ∷ _)  []       = false
eqNL (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eqNL xs ys

memNL : List ℕ → List (List ℕ) → Bool
memNL x []       = false
memNL x (y ∷ ys) = eqNL x y ∨ memNL x ys

nubGo : List (List ℕ) → List (List ℕ) → List (List ℕ)
nubGo seen []       = seen
nubGo seen (x ∷ xs) = nubGo (if memNL x seen then seen else x ∷ seen) xs

countNL : List ℕ → List (List ℕ) → ℕ
countNL x []       = 0
countNL x (y ∷ ys) = (if eqNL x y then 1 else 0) + countNL x ys

maxFib : List (List ℕ) → List (List ℕ) → ℕ
maxFib []       all = 0
maxFib (c ∷ cs) all = countNL c all ⊔ maxFib cs all

classesOf : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → List Desc
classesOf fuel e ins with jAt fuel e ins
... | _ , ds , _ , pre = map (bfilter (λ r → memN r pre)) ds

-- the first coordinate's range: how many distinct pre-state classes the
-- cascade's deliveries actually occupy.  `preClasses-bound` claims this
-- is at most 2 ^ cReg
mPre : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mPre fuel e ins = length (nubGo [] (classesOf fuel e ins))

-- the second coordinate's range: the largest fibre.  `fibreCap-bound`
-- claims this is at most cSize, and that claim is the DAMPER
mFib : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mFib fuel e ins =
  let cls = classesOf fuel e ins in maxFib (nubGo [] cls) cls

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
-- FOUR SHARED LEVELS, and this ladder exists for ONE question.  The
-- fibre of a pre-state class is capped at `2 ^ cReg` by `fibreCap-bound`
-- and MEASUREMENT 6 finds it ATTAINING that cap on the three-level lean
-- ladder — 128 against a 2 ^ cReg of 128, with the approach 8, 29, 64,
-- 99, 120, 127, 128.  A bound that is attained has no margin, and the
-- ratio of fibre to cap CLIMBS with ladder depth: 2/8, 13/32, 128/128 —
-- 0.25, 0.41, 1.00 at entry registries of 3, 5, 7.  Extrapolated, the
-- next rung breaks it.
--
-- So: same shape, one more shared level, entry registry 9, cap 512.  The
-- lean variant only — the accumulating one does not normalise past its
-- base rung two levels down, let alone here
------------------------------------------------------------------

Γˢ⁴ : Ctx 5
Γˢ⁴ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

insG⁴ : Slots Γˢ⁴
insG⁴ fz                             = shared (dup (input (fsuc fz)))
insG⁴ (fsuc fz)                      = shared (dup (input (fsuc (fsuc fz))))
insG⁴ (fsuc (fsuc fz))               = shared (dup (input (fsuc (fsuc (fsuc fz)))))
insG⁴ (fsuc (fsuc (fsuc fz)))        =
  shared (dup (input (fsuc (fsuc (fsuc (fsuc fz))))))
insG⁴ (fsuc (fsuc (fsuc (fsuc fz)))) = scripted (hot ((after 0 , 1) ∷ []))

mintOnly⁴ : ∀ {Θ} → ℕ → Tm Γˢ⁴ [] [] Θ (obs natᵗ)
mintOnly⁴ zero    = strmᵗ (input fz)
mintOnly⁴ (suc k) = strmᵗ (mergeAllᵉ (scanᵉ (mintOnly⁴ k) seedO (input fz)))

pL⁴ : ℕ → Closed Γˢ⁴ natᵗ
pL⁴ k = mergeAllᵉ (scanᵉ (mintOnly⁴ k) seedO (input fz))

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
-- THE DELIVERY GATE: every row above against `2 ^ cReg * cSize` at the
-- tightest caps the pre-state admits.  This is NOT the conjunct — the
-- conjunct bounds j, and MEASUREMENT 5 gates that — it is the FIRST of
-- the two factors: the claim that deliveries inject into (subsets of the
-- pre-state registry) × (an index below cSize).  Arithmetic over the
-- pinned numbers rather than a re-run of the evaluator per assertion.
--
-- The row that matters is `176 ≤ 2 ^ 7 * 18`, because the SAME row has
-- `176 > 2 ^ 7`: the second coordinate is doing real work, and without
-- it the bound is false rather than loose
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
-- THE ROUTE IS DEAD, and this is where it dies.  The derivation at the
-- `frameBlowup` site reads
--
--     deliveries ≤ 2 ^ cReg        frames per delivery ≤ cSize
--
-- and the LEFT one is false on a program three assertions above: L = 3
-- lean at k = 2 delivers 176 times out of an entry registry of 7.  The
-- DAG-path count is `2 ^ R_end`, the mint lifts R_end above cReg, and the
-- excess MATERIALISES rather than being damped away.  So the product
-- route does not merely lose slack, it loses the inequality: the
-- intermediate quantity `D * cSize` is itself over the old budget
------------------------------------------------------------------

_ : (176 ≤ᵇ 2 ^ 7) ≡ false
_ = refl

_ : (176 * 18 ≤ᵇ 2 ^ 7 * 18) ≡ false
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 5: THE FRAMES, which is what the conjunct bounds.  First
-- the mirror's faithfulness — it walks the evaluator's own state, so its
-- delivery ledger reproduces MEASUREMENT 3 — and then j itself
------------------------------------------------------------------

_ : mJdel 0 (pG′ 0) insG ≡ 5
_ = refl

_ : mJdel 0 (pG′² 0) insG² ≡ 20
_ = refl

_ : mJdel 0 (pL³ 0) insG³ ≡ 50
_ = refl

-- one shared level
_ : mJ 0 (pG′ 0) insG ≡ 8
_ = refl

_ : mJ 0 (pG′ 1) insG ≡ 10
_ = refl

_ : mJ 0 (pG′ 2) insG ≡ 10
_ = refl

-- two shared levels, accumulating and lean
_ : mJ 0 (pG′² 0) insG² ≡ 39
_ = refl

_ : mJ 0 (pG′² 1) insG² ≡ 85
_ = refl

_ : mJ 0 (pG′² 2) insG² ≡ 103
_ = refl

_ : mJ 0 (pG′² 3) insG² ≡ 105
_ = refl

_ : mJ 0 (pL² 0) insG² ≡ 20
_ = refl

_ : mJ 0 (pL² 2) insG² ≡ 51
_ = refl

_ : mJ 0 (pL² 4) insG² ≡ 53
_ = refl

-- three shared levels, lean: the sweep with the interior peak
_ : mJ 0 (pL³ 0) insG³ ≡ 58
_ = refl

_ : mJ 0 (pL³ 1) insG³ ≡ 226
_ = refl

_ : mJ 0 (pL³ 2) insG³ ≡ 548
_ = refl

_ : mJ 0 (pL³ 3) insG³ ≡ 912
_ = refl

_ : mJ 0 (pL³ 4) insG³ ≡ 1164
_ = refl

_ : mJ 0 (pL³ 5) insG³ ≡ 1268
_ = refl

_ : mJ 0 (pL³ 6) insG³ ≡ 1291
_ = refl

-- and the tightest single point in the file against the OLD count
_ : mJ 0 (pG′³ 0) insG³ ≡ 324
_ = refl

-- across instants
_ : mJ 1 (pG′ 0) insG ≡ 29
_ = refl

_ : mJ 2 (pG′ 0) insG ≡ 86
_ = refl

_ : mJ 1 (pG′ 2) insG ≡ 91
_ = refl

------------------------------------------------------------------
-- THE FRAME GATE: j against `2 ^ cReg * cSize * cSize`, the count the
-- two factors actually give.  The lean L = 3 ladder is the whole sweep
-- because it is the one whose ratio climbs before it falls
------------------------------------------------------------------

-- one shared level, k = 0 … 2 at (3, 8)
_ : (10 ≤ᵇ 2 ^ 3 * 8 * 8) ≡ true
_ = refl

-- two shared levels, accumulating, k = 0 … 3 at (5, {8,22,36,50})
_ : (39 ≤ᵇ 2 ^ 5 * 8 * 8) ≡ true
_ = refl

_ : (85 ≤ᵇ 2 ^ 5 * 22 * 22) ≡ true
_ = refl

_ : (103 ≤ᵇ 2 ^ 5 * 36 * 36) ≡ true
_ = refl

_ : (105 ≤ᵇ 2 ^ 5 * 50 * 50) ≡ true
_ = refl

-- two shared levels, lean, k = 0, 2, 4 at (5, {3,18,34})
_ : (20 ≤ᵇ 2 ^ 5 * 3 * 3) ≡ true
_ = refl

_ : (51 ≤ᵇ 2 ^ 5 * 18 * 18) ≡ true
_ = refl

_ : (53 ≤ᵇ 2 ^ 5 * 34 * 34) ≡ true
_ = refl

-- three shared levels, lean, k = 0 … 6 at (7, {3,10,18,26,34,42,50})
_ : (58 ≤ᵇ 2 ^ 7 * 3 * 3) ≡ true
_ = refl

_ : (226 ≤ᵇ 2 ^ 7 * 10 * 10) ≡ true
_ = refl

_ : (548 ≤ᵇ 2 ^ 7 * 18 * 18) ≡ true
_ = refl

_ : (912 ≤ᵇ 2 ^ 7 * 26 * 26) ≡ true
_ = refl

_ : (1164 ≤ᵇ 2 ^ 7 * 34 * 34) ≡ true
_ = refl

_ : (1268 ≤ᵇ 2 ^ 7 * 42 * 42) ≡ true
_ = refl

_ : (1291 ≤ᵇ 2 ^ 7 * 50 * 50) ≡ true
_ = refl

-- the accumulating three-level ladder, and across instants
_ : (324 ≤ᵇ 2 ^ 7 * 8 * 8) ≡ true
_ = refl

_ : (29 ≤ᵇ 2 ^ 6 * 21 * 21) ≡ true
_ = refl

_ : (91 ≤ᵇ 2 ^ 7 * 77 * 77) ≡ true
_ = refl

------------------------------------------------------------------
-- THE WORST RATIO IN THE FILE, and it is at k = 0 — the NON-nested mint,
-- the shape family G already gated.  Nesting is not the escape
-- direction, though it is not as flatly safe as the delivery counts
-- alone suggested: j peaks at k = 3 on the lean L = 3 ladder before it
-- falls, so the margin narrows over three rungs and then widens again.
--
--     against the NEW count `2 ^ cReg * cSize * cSize`
--       L = 3, k = 0, accumulating   324 / (2 ^ 7 * 8 * 8)  = 0.040
--       L = 3, k = 0, lean            58 / (2 ^ 7 * 3 * 3)  = 0.050
--       L = 3, k = 3, lean           912 / (2 ^ 7 * 26 * 26) = 0.011
--
-- stated as the comparison a ratio ten times worse would break
------------------------------------------------------------------

_ : (324 * 10 ≤ᵇ 2 ^ 7 * 8 * 8) ≡ true
_ = refl

_ : (58 * 10 ≤ᵇ 2 ^ 7 * 3 * 3) ≡ true
_ = refl

_ : (912 * 10 ≤ᵇ 2 ^ 7 * 26 * 26) ≡ true
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 6: THE TWO COORDINATES, AND THE DAMPER AS FIRST STATED
-- IS FALSE.
--
-- `cascadeGo-deliveries` sends a delivery to (its pre-state class, an
-- index), `preClasses-bound` caps the first coordinate at 2 ^ cReg and
-- `fibreCap-bound` caps the second.  The second was first stated at
-- cSize, on the reasoning that a mint happens inside ONE frame and a
-- frame's step function names no more sources than its syntax holds.
-- Measured, that is wrong twice — and wrong on the LEAN families, which
-- is the point of them: they keep the whole delivery structure while
-- shrinking the syntax the cap is read off.
--
--   program   cReg  cSize    D   mPre  2^cReg   mFib
--   pG′  0      3      8     5      4      8      2
--   pG′  1      3     22     5      4      8      2
--   pG′  2      3     36     5      4      8      2
--   pG′² 0      5      8    20     10     32      7
--   pG′² 1      5     22    26     10     32     12
--   pG′² 2      5     36    27     10     32     13
--   pL²  0      5      3    16     10     32      4     ← 4 > 3
--   pL²  2      5     18    21     10     32      8
--   pL²  4      5     34    21     10     32      8
--   pL³  0      7      3    50     22    128      8     ← 8 > 3
--
-- WHAT REPLACES IT.  Both coordinates now range over subsets of the
-- ENTRY registry: a delivery is determined by the pre-state
-- registrations it visits TOGETHER WITH the pre-state registrations
-- whose dispatches minted the ones it visits.  Every mint happens during
-- some delivery and every delivery bottoms out at a pre-state chain, so
-- the second coordinate is pre-state data too — which is a story rather
-- than a curve fit, though it is still only a story: it is not a proof
-- that the recursion bottoms out, and `fibreCap-bound` is postulated.
-- The count becomes `2 ^ cReg * 2 ^ cReg * cSize`.
--
-- Note the first coordinate is nowhere near its cap (22 against 128) and
-- the second is nowhere near the new one (13 against 32).  It is the
-- SHAPE that is at issue, not the slack
------------------------------------------------------------------

-- one descriptor per delivery, which is what makes them a reindexing of
-- the ledger rather than a separate walk
_ : mJdesc 0 (pG′ 0) insG ≡ 5
_ = refl

_ : mJdesc 0 (pG′² 0) insG² ≡ 20
_ = refl

_ : mPre 0 (pG′ 0) insG ≡ 4
_ = refl

_ : mFib 0 (pG′ 0) insG ≡ 2
_ = refl

_ : mPre 0 (pG′ 1) insG ≡ 4
_ = refl

_ : mFib 0 (pG′ 1) insG ≡ 2
_ = refl

_ : mPre 0 (pG′ 2) insG ≡ 4
_ = refl

_ : mFib 0 (pG′ 2) insG ≡ 2
_ = refl

_ : mS 0 (pG′ 2) insG ≡ 36
_ = refl

_ : mPre 0 (pG′² 0) insG² ≡ 10
_ = refl

_ : mFib 0 (pG′² 0) insG² ≡ 7
_ = refl

_ : mPre 0 (pG′² 1) insG² ≡ 10
_ = refl

_ : mFib 0 (pG′² 1) insG² ≡ 12
_ = refl

_ : mPre 0 (pG′² 2) insG² ≡ 10
_ = refl

_ : mFib 0 (pG′² 2) insG² ≡ 13
_ = refl

_ : mPre 0 (pL² 0) insG² ≡ 10
_ = refl

_ : mFib 0 (pL² 0) insG² ≡ 4
_ = refl

_ : mPre 0 (pL² 2) insG² ≡ 10
_ = refl

_ : mFib 0 (pL² 2) insG² ≡ 8
_ = refl

_ : mPre 0 (pL² 4) insG² ≡ 10
_ = refl

_ : mFib 0 (pL² 4) insG² ≡ 8
_ = refl

_ : mPre 0 (pL³ 0) insG³ ≡ 22
_ = refl

_ : mFib 0 (pL³ 0) insG³ ≡ 8
_ = refl

-- THE LADDER SWEEP, which is where the second coordinate does all its
-- growing.  mPre is CONSTANT down each ladder — 4, 10, 22 for entry
-- registries of 3, 5, 7 — because the pre-state classes are fixed by the
-- pre-state DAG, exactly as the damper's story says.  Every bit of the
-- k-dependence lands in the fibre, and on the three-level lean ladder it
-- climbs to EXACTLY 2 ^ cReg and stops
_ : mPre 0 (pG′² 3) insG² ≡ 10
_ = refl

_ : mFib 0 (pG′² 3) insG² ≡ 13
_ = refl

_ : mPre 0 (pL³ 1) insG³ ≡ 22
_ = refl

_ : mFib 0 (pL³ 1) insG³ ≡ 29
_ = refl

_ : mPre 0 (pL³ 2) insG³ ≡ 22
_ = refl

_ : mFib 0 (pL³ 2) insG³ ≡ 64
_ = refl

_ : mFib 0 (pL³ 3) insG³ ≡ 99
_ = refl

_ : mFib 0 (pL³ 4) insG³ ≡ 120
_ = refl

_ : mFib 0 (pL³ 5) insG³ ≡ 127
_ = refl

_ : mPre 0 (pL³ 6) insG³ ≡ 22
_ = refl

_ : mFib 0 (pL³ 6) insG³ ≡ 128
_ = refl

_ : mPre 0 (pG′³ 0) insG³ ≡ 22
_ = refl

_ : mFib 0 (pG′³ 0) insG³ ≡ 29
_ = refl

-- THE REFUTATION: the fibre is over cSize on both lean families
_ : (4 ≤ᵇ 3) ≡ false
_ = refl

_ : (8 ≤ᵇ 3) ≡ false
_ = refl

-- AND THE REPAIRED BOUNDS: both coordinates under 2 ^ cReg
_ : (4 ≤ᵇ 2 ^ 3) ≡ true
_ = refl

_ : (2 ≤ᵇ 2 ^ 3) ≡ true
_ = refl

_ : (10 ≤ᵇ 2 ^ 5) ≡ true
_ = refl

_ : (13 ≤ᵇ 2 ^ 5) ≡ true
_ = refl

_ : (22 ≤ᵇ 2 ^ 7) ≡ true
_ = refl

_ : (8 ≤ᵇ 2 ^ 7) ≡ true
_ = refl

-- and the row where the second coordinate is EXACTLY at its cap.  The
-- fibre down the lean three-level ladder runs 8, 29, 64, 99, 120, 127,
-- 128 against a 2 ^ cReg of 128: the bound is ATTAINED, so it is tight —
-- no smaller function of cReg can replace it — and there is no margin
-- left in it either
_ : (128 ≤ᵇ 2 ^ 7) ≡ true
_ = refl

_ : (129 ≤ᵇ 2 ^ 7) ≡ false
_ = refl

-- and the count they give, against the worst j in the file
_ : (324 ≤ᵇ 2 ^ 7 * 2 ^ 7 * 8) ≡ true
_ = refl

_ : (1291 ≤ᵇ 2 ^ 7 * 2 ^ 7 * 50) ≡ true
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 7: THE LADDER RUNG THAT KILLS THE SPLIT.
--
-- MEASUREMENT 6 found the fibre ATTAINING `2 ^ cReg` on the three-level
-- lean ladder — 128 against 128 — and a bound that is attained has no
-- margin.  It also found the ratio of fibre to cap climbing with ladder
-- depth: 2/8, 13/32, 128/128.  So this runs one more rung.
--
--   program   cReg  cSize     D   mPre  2^cReg   mFib
--   pL⁴ 0       9      3    166     46     512     16
--   pL⁴ 1       9     10    726     46     512    121
--   pL⁴ 2       9     18   2546     46     512    576   ← 576 > 512
--
-- `fibreCap ≤ 2 ^ cReg` IS FALSE.  The second coordinate is not
-- pre-state data, and no constant multiple of `2 ^ cReg` is safe either:
-- the ratio runs 0.25, 0.41, 1.00, 1.13 and is still climbing.
--
-- THE FIRST COORDINATE, BY CONTRAST, IS EXACTLY WHAT THE STORY SAID.
-- mPre is 4, 10, 22, 46 down the four ladders — `3 * 2 ^ L - 2`, with an
-- entry registry of `2L + 1`, so it is about `2 ^ (cReg / 2)` and sits at
-- a QUARTER of its cap's exponent.  And it is invariant in k: the
-- pre-state classes are fixed by the pre-state DAG and minting adds none.
--
-- SO THE SPLIT IS DEAD, and it is dead for a reason worth writing down.
-- D = mPre * (fibre), mPre is small and genuinely pre-state, and the
-- fibre is therefore essentially D itself — 2546 deliveries over 46
-- classes, worst class 576.  Splitting D into (something small) times
-- (something the size of D) renames the problem instead of decomposing
-- it.  Two bounds on that second factor have now been measured false in
-- one session, and the honest conclusion is that the delivery count has
-- to be bounded WHOLE.
--
-- What survives, on every row in this file and with the ratio FALLING as
-- the ladder deepens (0.078, 0.026, 0.016, 0.0097), is
--
--     D ≤ 2 ^ cReg * 2 ^ cReg
--
-- which is what `cascadeGo-deliveries` now states, unsplit
------------------------------------------------------------------

_ : mReg 0 (pL⁴ 0) insG⁴ ≡ 9
_ = refl

_ : mReg 0 (pL⁴ 1) insG⁴ ≡ 9
_ = refl

_ : mReg 0 (pL⁴ 2) insG⁴ ≡ 9
_ = refl

_ : mS 0 (pL⁴ 0) insG⁴ ≡ 3
_ = refl

_ : mS 0 (pL⁴ 1) insG⁴ ≡ 10
_ = refl

_ : mS 0 (pL⁴ 2) insG⁴ ≡ 18
_ = refl

_ : mFolds 0 (pL⁴ 0) insG⁴ ≡ 166
_ = refl

_ : mFolds 0 (pL⁴ 1) insG⁴ ≡ 726
_ = refl

_ : mFolds 0 (pL⁴ 2) insG⁴ ≡ 2546
_ = refl

_ : mPre 0 (pL⁴ 0) insG⁴ ≡ 46
_ = refl

_ : mPre 0 (pL⁴ 1) insG⁴ ≡ 46
_ = refl

_ : mFib 0 (pL⁴ 0) insG⁴ ≡ 16
_ = refl

_ : mFib 0 (pL⁴ 1) insG⁴ ≡ 121
_ = refl

_ : mFib 0 (pL⁴ 2) insG⁴ ≡ 576
_ = refl

-- THE REFUTATION, on the pinned numbers: the fibre is over 2 ^ cReg
_ : (576 ≤ᵇ 2 ^ 9) ≡ false
_ = refl

-- THE FIRST COORDINATE, still far inside its cap on the same row
_ : (46 ≤ᵇ 2 ^ 9) ≡ true
_ = refl

-- AND THE UNSPLIT DELIVERY BOUND, which every row of the file gates and
-- whose margin GROWS with ladder depth rather than shrinking
_ : (5 ≤ᵇ 2 ^ 3 * 2 ^ 3) ≡ true
_ = refl

_ : (27 ≤ᵇ 2 ^ 5 * 2 ^ 5) ≡ true
_ = refl

_ : (269 ≤ᵇ 2 ^ 7 * 2 ^ 7) ≡ true
_ = refl

_ : (2546 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ true
_ = refl

-- stated as the comparison a ratio ten times worse would break, at the
-- deepest ladder measured
_ : (2546 * 10 ≤ᵇ 2 ^ 9 * 2 ^ 9) ≡ true
_ = refl
