------------------------------------------------------------------
-- THE MINT-LOOP SHAPES AND MEASURES.  Split out of Mint-Loop-Probe so
-- that measuring costs only the evaluator: every `refl` wall lives next
-- door, and `scripts/measure.sh` imports THIS module, so reading one
-- number off a normal form no longer pays for the whole file's pins.
--
-- The narrative — what these families are for and what they settled — is
-- at the head of Mint-Loop-Probe.  Nothing here is checked by anything
-- here; the assertions that give these definitions their meaning are all
-- in that file.
------------------------------------------------------------------
module Mint-Loop-Shapes where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤ᵇ_; _≡ᵇ_; _⊔_)
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

------------------------------------------------------------------
-- R_end, AND IT DECIDES WHICH PROOF TECHNOLOGY THE DELIVERY BOUND GETS.
--
-- `cascadeGo-deliveries` says `D ≤ 2 ^ cReg * 2 ^ cReg` and has margin
-- without a route.  The DAG a delivery path runs through is the registry
-- AS OF THE DISPATCH, not at entry, so the inverted-pair argument — the
-- one leg that has never failed — proves `D ≤ 2 ^ R_end`, and whether
-- that is usable turns entirely on what R_end is:
--
--   · if the mints are bounded by entry data, `2 ^ R_end ≤ 4 ^ cReg`
--     lands the bound nearly verbatim and the grind starts on the
--     inverted pair;
--   · if the mints track the DELIVERIES, every subset-injection route is
--     dead for this bound whether or not it is true, and the proof has to
--     be what the damper natively is — an ORDERING fact, a
--     schedule-indexed induction on a decreasing remaining-dispatch
--     potential, not a statement about sets.
--
-- Registrations mint ids in order, so the mint count is just the
-- watermark's travel: `nextReg` after the cascade less `nextReg` before.
-- No threading, and it rides the `postAt` this file already computes.
--
-- THE READING, and it is the second outcome, unambiguously:
--
--   program   cReg      D   mints   mints/D
--   pG′  0      3      5       3      0.60
--   pG′  2      3      5       4      0.80
--   pG′² 0      5     20      10      0.50
--   pG′² 3      5     27      33      1.22
--   pL²  0      5     16       4      0.25
--   pL²  4      5     21      15      0.71
--   pL³  0      7     50       8      0.16
--   pL³  2      7    176      92      0.52
--   pL³  6      7    269     254      0.94
--
-- MINTS TRACK DELIVERIES.  At the deepest rung measured nearly every
-- delivery mints, and the registry the cascade LEAVES is 261 against an
-- entry cReg of 7 — thirty-seven times the entry registry, and it climbs
-- with the ladder.  R_end is not entry-computable by any margin.
--
-- SO EVERY SUBSET-INJECTION ROUTE IS DEAD FOR THE DELIVERY BOUND,
-- whether or not the bound is true.  The inverted-pair argument still
-- proves `D ≤ 2 ^ R_end` — it is the one leg that has never failed — but
-- at R_end = 261 that is 2 ^ 261 against a budget of 2 ^ 18, so it
-- proves nothing usable.  It also explains the fibre refutation
-- structurally rather than numerically: the minted registrations are
-- D-many, so the "second coordinate" was ranging over a set of size
-- 2 ^ D and never had a chance of sitting under 2 ^ cReg.
--
-- WHAT IS LEFT IS WHAT THE DAMPER NATIVELY IS: an ordering fact, not a
-- statement about sets.  A minted registration is reachable only by
-- dispatches that come AFTER it, so the proof wants a schedule-indexed
-- induction on a decreasing potential — the remaining-dispatch count,
-- fixed at each point by the DAG-so-far — rather than an injection into
-- anything.  That is different machinery from every route tried so far,
-- and this measurement is what says so before the grind rather than
-- after it
------------------------------------------------------------------

-- registrations MINTED during the one cascade
mMints : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mMints fuel e ins =
  EvalSt.nextReg (postAt fuel e ins) ∸ EvalSt.nextReg (proj₂ (stAt fuel e ins))

-- and the registry the cascade leaves behind (after cascadeFinish's
-- drop-and-sweep, so it is a floor on the DAG, not the peak)
mRegEnd : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mRegEnd fuel e ins = length (EvalSt.registry (postAt fuel e ins))

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

