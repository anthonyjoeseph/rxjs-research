-- ROADMAP: ROUTE GUARD — the measured store-growth rows the caps tower must keep dominating (Caps-Face.agda:4836).
-- DELETE WHEN: The-Proof.agda is discharged — a dead route cannot be retried once the proof is done  [T7]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
------------------------------------------------------------------
-- THE INSTANT-HEIGHT PROBE: how fast do the STORE's two axes climb
-- ACROSS INSTANTS, and does the receipt's payload width V stay under
-- what the PREVIOUS instant left in the store?
--
-- WHY IT EXISTS.  Charge-Probe refuted `j ≤ D * cSize` and measured the
-- form the receipt table dictates,
--
--     j ≤ D * cSize * suc (cWid * suc cSize)
--
-- which fits every row it has.  But the count may NOT read cWid
-- (Width-Count-Probe: a count with a cWid summand iterates the tower
-- function once per instant and capsAt-tower's linear height is gone),
-- so if that form is to be the charge, the `cWid` factor has to be
-- served by cSize's OWN growth across instants instead.  Whether that
-- can work is a question about REAL GROWTH RATES between instants, and
-- nothing in the tree has ever measured them.  This probe measures
-- them.
--
-- WHAT IS MEASURED, per instant id (id = the cascade index; `drainSt`
-- runs one cascade per arrival and hands the evaluator that same index
-- as its Id, so cascade i IS instant i):
--
--   V(id)   VMAX: the largest `length vals` crossing any map-f/scan-f
--           frame during instant id's cascade.  Read off a read-only
--           mirror of foldPath / dispatchShare / shareGo / cascadeGo
--           that calls the REAL stepFrame — Charge-Probe's pattern — so
--           the state it walks is the state the evaluator walks.
--   J(id)   the RECEIPT-WEIGHTED j, Charge-Probe's cJ, recomputed by
--           the same walk (so V and J come off ONE traversal and J
--           doubles as that walk's calibration against Charge-Probe's
--           own pins).
--   F(id)   the same walk counting ONE per frame — Mint-Loop-Shapes' mJ.
--   D(id)   deliveries, off the evaluator's ledger (mFolds).
--   S(id)   the tightest cSize the PRE-cascade state admits (mS id).
--   W(id)   the tightest cWid the PRE-cascade state admits (mW id) —
--           which is WSTORE(id − 1), the width the previous instant left.
--   S⁺(id)  SSTORE: the tightest cSize at the END of instant id, i.e.
--           mS (suc id).
--   W⁺(id)  WSTORE: the tightest cWid at the END of instant id, i.e.
--           mW (suc id).
--
-- BOTH V AND J ARE LOWER BOUNDS, for the same reason Charge-Probe's cJ
-- is: the walk counts the *All edges as one and never sees the frames
-- `subscribeE` steps when a from-inner / thru-outer frame re-enters it.
-- A row that BREACHES a gate breaches it for real; a row that fits is
-- evidence and not a proof.
--
-- THE FOUR RATIOS THE DESIGN NEEDS, and NOTHING is read off them here
-- beyond the tables themselves:
--
--   (e1)  V(id)  vs  W(id)          — is the arriving payload width
--                                     bounded by what the previous
--                                     instant STORED?
--   (e2)  W⁺(id) vs story (W(id))   — Frame-Work-Probe's per-arrival
--                                     law wₖ₊₁ = 2 ^ (wₖ + 1) ∸ 2, i.e.
--                                     is real width climb ≤ ONE story
--                                     per instant?
--   (e3)  J(id)  vs  D(id) * S(id) * suc (V(id) * suc (S(id)))
--                                   — the receipt-dictated charge with
--                                     the MEASURED V in place of cWid.
--   (e4)  S⁺(id) vs  iterSize (S id) (D * S * suc V) (S id)
--                                   — does the SIZE axis absorb V-many
--                                     folds per frame at a polynomial
--                                     count?  Measured as `sNeed`, the
--                                     MINIMAL number of sizeStep passes
--                                     that reaches S⁺, against the count
--                                     the form allows: the RHS itself is
--                                     a 10^100-digit numeral at these
--                                     counts and reporting the minimal
--                                     pass count says strictly more.
--
-- PROVENANCE IS THREE-STATE and marked on every row: `refl` (pinned by
-- the typechecker below), `compiled` (measured-not-rechecked through
-- probe/Instant-Height-Main.agda and the GHC backend), and NOT MEASURED
-- (killed, with the wall and the time recorded).
--
-- Standalone, so src/Main.agda never reaches it.  It imports
-- Mint-Loop-Shapes' harness and Charge-Probe's width denominator and
-- width-heavy programs rather than repeating either.
------------------------------------------------------------------
module Instant-Height-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤ᵇ_; _⊔_)
open import Data.Nat.DivMod using (_/_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; length; map; any; foldr)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin; toℕ) renaming (zero to fz; suc to fsuc)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; Tick; Gas; after_,_; hot)
open import Rx.Exp  using (Ctx; Closed; Exp; Tm; Fn; Val; natᵗ; obs; _×ᵗ_;
                           input; ofᵉ; mergeAllᵉ; scanᵉ; μᵉ; deferᵉ; varᵉ;
                           strmᵗ; nat̂; sizeᵗ)
open import Rx.Evaluator using (Slots; scripted; Sched; EvalSt;
                                sched-next; budgetAt;
                                root; Path; share-sink; _↠_;
                                Frame; map-f; scan-f; take-f;
                                from-inner; thru-outer;
                                RegId; Arrival; arrTy; arrVal; arrTick;
                                stepFrame; shareAdmit; shareLatch; shareFinish;
                                chainsOf; cascadeLatch)

-- the four caps-arithmetic functions moved to Rx.Evaluator when the
-- Verify-Budget-Sufficient umbrella was split (a8508d6)
open import Rx.Evaluator using (sizeStep; foldStep; iterSize; iterFold)

open import Mint-Loop-Shapes
  using (runSt; stAt; mS; mReg; mFolds; mJ;
         accV; seedO;
         Γˢ¹; insG; Γˢ²; insG²; Γˢ³; insG³;
         pL²; pL³)

open import Charge-Probe
  using (frameJ; mW; deepScan; wrap3; progD; progDT; progW; pF1; pF2;
         Γ₀; Γ₁; ins₀; insD₁; insD₂)

------------------------------------------------------------------
-- (a) THE PAYLOAD WIDTH, off the same walk as the receipt.
--
-- `frameV` is the receipt's own `length vals` — the V of
-- `scanFrame-caps`'s `j′ = suc (length vals * suc (sizeᵗ fn))` — read at
-- the frames that actually charge for it.  take-f charges 0 and the two
-- *All edges delegate, so neither contributes a V.
------------------------------------------------------------------

frameV : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → List (Val Γ s) → ℕ
frameV (map-f _)          vals = length vals
frameV (scan-f _ _)       vals = length vals
frameV (take-f _)         vals = 0
frameV (from-inner _ _ _) vals = 0
frameV (thru-outer _ _)   vals = 0

------------------------------------------------------------------
-- THE MIRROR, Charge-Probe's `wfp` carrying a PAIR: the receipt-weighted
-- j and the running maximum of `frameV`.  One traversal, so the j
-- coordinate is a free calibration against Charge-Probe's pins
------------------------------------------------------------------

JV : Set
JV = ℕ × ℕ

_⊕_ : JV → JV → JV
(j₁ , v₁) ⊕ (j₂ , v₂) = j₁ + j₂ , v₁ ⊔ v₂

ifp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    → Gas → ℕ → Id → Tick
    → Path Γ u t → List (Val Γ u) → Bool
    → Sched Γ → EvalSt e → JV × Sched Γ × EvalSt e

ids : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Gas → ℕ → Id → Tick → (i : Fin n)
    → List (Val Γ (Data.Vec.lookup Γ i)) → Bool
    → Sched Γ → EvalSt e → JV × Sched Γ × EvalSt e

isg : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Gas → ℕ → Id → Tick → (i : Fin n)
    → List (Val Γ (Data.Vec.lookup Γ i)) → Bool
    → List (RegId × Path Γ (Data.Vec.lookup Γ i) t)
    → Sched Γ → EvalSt e → JV × Sched Γ × EvalSt e

ifp sf gas id now root vals fin sched st = (0 , 0) , sched , st
ifp sf gas id now (share-sink i) vals fin sched st =
  ids sf gas id now i vals fin sched st
ifp sf gas id now (f ↠ p) vals fin sched st =
  let (vals′ , _ , fin′ , sched₁ , st₁) = stepFrame sf id now f p vals fin sched st
      (m , sched₂ , st₂) = ifp sf gas id now p vals′ fin′ sched₁ st₁
  in ((frameJ f vals , frameV f vals) ⊕ m) , sched₂ , st₂

ids sf zero      id now i vals fin sched st = (0 , 0) , sched , st
ids sf (suc gas) id now i vals fin sched st =
  let (m , sched₁ , st₁) =
        isg sf gas id now i vals fin
          (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)
      (_ , sched₂ , st₂) = shareFinish i fin ([] , sched₁ , st₁)
  in m , sched₂ , st₂

isg sf gas id now i vals fin []               sched st = (0 , 0) , sched , st
isg sf gas id now i vals fin ((rid , p) ∷ ps) sched st
  with any (Data.Nat._≡ᵇ_ rid) (EvalSt.cancelled st)
... | true  = isg sf gas id now i vals fin ps sched st
... | false =
  let (m₁ , sched₁ , st₁) =
        ifp sf gas id now p vals fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
      (m₂ , sched₂ , st₂) = isg sf gas id now i vals fin ps sched₁ st₁
  in (m₁ ⊕ m₂) , sched₂ , st₂

ics : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → (a : Arrival Γ) → Id → List (RegId × Path Γ (arrTy a) t)
    → Sched Γ → EvalSt e → JV × Sched Γ × EvalSt e
ics a id []                   sched st = (0 , 0) , sched , st
ics {n = n} {e = e} a id ((rid , c) ∷ chains) sched st
  with any (Data.Nat._≡ᵇ_ rid) (EvalSt.cancelled st)
... | true  = ics a id chains sched st
... | false =
  let (m₁ , sched₁ , st₁) =
        ifp (budgetAt e (Sched.slots sched) id) n id (arrTick a) c
            (arrVal a ∷ []) (Arrival.isLast a) sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
      (m₂ , sched₂ , st₂) = ics a id chains sched₁ st₁
  in (m₁ ⊕ m₂) , sched₂ , st₂

iAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → JV
iAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = 0 , 0
...   | inj₂ (a , sched′) = proj₁ (ics a nid (chainsOf a st) sched′ (cascadeLatch a st))

-- (a) VMAX: the largest payload-list length crossing a charging frame
-- during instant id's cascade
iV : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
iV fuel e ins = proj₂ (iAt fuel e ins)

-- (d) J: the receipt-weighted j of instant id's cascade.  Same walk, so
-- pinning this against Charge-Probe's cJ calibrates VMAX for free
iJ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
iJ fuel e ins = proj₁ (iAt fuel e ins)

------------------------------------------------------------------
-- (b) and (c) THE STORED AXES AT THE END OF AN INSTANT.  `stAt k`
-- drains k cascades, so the state at the END of instant id is `stAt
-- (suc id)` — which makes WSTORE and SSTORE the SAME functions mW and mS
-- read one fuel further on.  Nothing new is needed, and the pre-state
-- reading W(id) = mW id is definitionally WSTORE(id ∸ 1)
------------------------------------------------------------------

wStore : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
wStore id e ins = mW (suc id) e ins

sStore : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
sStore id e ins = mS (suc id) e ins

------------------------------------------------------------------
-- (e) THE RATIO MACHINERY.
--
-- `story` is Frame-Work-Probe's measured per-arrival law, wₖ₊₁ =
-- 2 ^ (wₖ + 1) ∸ 2 — ONE story of the tower per instant.
--
-- `sNeed` / `wNeed` are the minimal pass counts: how many sizeStep /
-- foldStep applications at base S it takes to reach a target from a
-- start.  They are what (e4) wants reported, because the count the
-- charge form allows is in the thousands and `iterSize S 1000 S` is a
-- numeral with more digits than there are atoms — the minimal pass count
-- is the same comparison, computable, and strictly more informative.
-- Fuel 64 is a ceiling: a returned 64 means "not reached in 64 passes",
-- which cannot happen for any target these programs produce (sizeStep at
-- least doubles).
------------------------------------------------------------------

story : ℕ → ℕ
story w = 2 ^ suc w ∸ 2

sNeedGo : ℕ → ℕ → ℕ → ℕ → ℕ
sNeedGo zero       S target s = 0
sNeedGo (suc fuel) S target s =
  if target ≤ᵇ s then 0 else suc (sNeedGo fuel S target (sizeStep S s))

-- minimal k with `iterSize S k s ≥ target`
sNeed : ℕ → ℕ → ℕ → ℕ
sNeed S target s = sNeedGo 64 S target s

wNeedGo : ℕ → ℕ → ℕ → ℕ → ℕ
wNeedGo zero       S target w = 0
wNeedGo (suc fuel) S target w =
  if target ≤ᵇ w then 0 else suc (wNeedGo fuel S target (foldStep S w))

-- minimal k with `iterFold S k w ≥ target`
wNeed : ℕ → ℕ → ℕ → ℕ
wNeed S target w = wNeedGo 8 S target w

-- the count the receipt-dictated charge allows at instant id
jForm : ℕ → ℕ → ℕ → ℕ
jForm D S V = D * S * suc (V * suc S)

------------------------------------------------------------------
-- THE FAMILIES.
--
-- Every one is a TOWER family — a program whose stored width or size is
-- meant to climb between instants — plus one mint ladder for contrast,
-- where the deliveries are many and the payloads are one wide.
--
-- The deepening scan and the tripling scan come from Charge-Probe (which
-- took them from Frame-Work-Probe and Fold-Count-Probe); only the SCRIPTS
-- are new, because an instant sweep needs four arrivals where the charge
-- rows needed one.  `insD⁴` is `insD₂` with two more emissions, which
-- also moves `Arrival.isLast` on the earlier arrivals — so the id = 0
-- rows under insD₂ and insD⁴ are not automatically the same program's,
-- and both are measured
------------------------------------------------------------------

insD⁴ : Slots Γ₁
insD⁴ fz = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ (after 0 , 3)
                           ∷ (after 0 , 4) ∷ []))

------------------------------------------------------------------
-- THE μ FAMILY — Eval-Growth-Probe's §4/§5 ladder ADAPTED TO RUN.
--
-- There the μ is measured statically: `dWᵉ (unfoldμ (μbody m))` doubles
-- per rung while every entry quantity moves by a constant, and §5 shows
-- two `foldStep` passes swallow it.  Nothing there RUNS, so nothing
-- there says what a μ does to the STORE across instants.  Here the same
-- shape is run: `ticker` is Frame-Work-Probe's defer loop — one value
-- now, itself next tick, forever, with NO scripted input at all — and it
-- is fed to the two amplifiers.  This is the one family whose arrivals
-- are minted by the program rather than by a script
------------------------------------------------------------------

ticker : Closed Γ₀ natᵗ
ticker = μᵉ (mergeAllᵉ (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
                            ∷ strmᵗ (deferᵉ (varᵉ (here refl))) ∷ [])))

-- the doubling wrap over the ticker: Frame-Work-Probe's `feedback`
pμ2 : Closed Γ₀ natᵗ
pμ2 = mergeAllᵉ (scanᵉ wrap3 seedO ticker)

-- and the deepening scan over the ticker, which is the sharpest
-- amplifier over the one arrival source no script controls
pμD : Closed Γ₀ natᵗ
pμD = mergeAllᵉ (scanᵉ deepScan seedO ticker)

------------------------------------------------------------------
-- ONE INSTANT'S WHOLE ROW, in the order the tables below print it:
--
--     V  J  F  D  S  W  S⁺  W⁺
--
-- so that a family's instant sweep is one measurement per instant
-- rather than eight.  Both harnesses read this: the compiled one prints
-- it, the `refl` wall pins it
------------------------------------------------------------------

tup : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → List ℕ
tup id e ins =
    iV     id e ins
  ∷ iJ     id e ins
  ∷ mJ     id e ins
  ∷ mFolds id e ins
  ∷ mS     id e ins
  ∷ mW     id e ins
  ∷ sStore id e ins
  ∷ []

-- W⁺ IS ITS OWN ROW, because on the deepening families it is the one
-- quantity that stops being a number: progDT's stored width is 3072 at
-- the end of instant 1 and a 1000-digit numeral at the end of instant 2,
-- so instant 3 asks for a numeral with 10^1000 digits and no harness
-- reaches it.  Splitting it off keeps the other seven columns measurable
-- at an instant where it is not
digitsGo : ℕ → ℕ → ℕ
digitsGo zero       m = 0
digitsGo (suc fuel) m = if m ≤ᵇ 9 then 1 else suc (digitsGo fuel (m / 10))

wDig : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
wDig id e ins = digitsGo 1000000 (wStore id e ins)

-- THE CASCADE HALF ALONE — V J F D S W, everything that is read at or
-- before instant id, with the two END-of-instant columns dropped.  It
-- exists because the wall is not where it looks: on the width-heavy
-- families the tuple dies, and splitting it says whether it died running
-- the cascade or measuring the store afterwards
cas : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → List ℕ
cas id e ins =
    iV     id e ins
  ∷ iJ     id e ins
  ∷ mJ     id e ins
  ∷ mFolds id e ins
  ∷ mS     id e ins
  ∷ mW     id e ins
  ∷ []

------------------------------------------------------------------
-- THE ROWS.
--
-- Columns, in `tup` order, all at instant id:
--
--   V   VMAX      the largest payload-list length crossing a map-f /
--                 scan-f frame in instant id's cascade  (LOWER BOUND)
--   J   the receipt-weighted j of that cascade           (LOWER BOUND)
--   F   the same walk counting one per frame  (= mJ)
--   D   deliveries  (= mFolds)
--   S   the tightest cSize the PRE-cascade state admits  (= mS id)
--   W   the tightest cWid  the PRE-cascade state admits  (= mW id),
--       which IS WSTORE(id ∸ 1)
--   S⁺  SSTORE(id): the tightest cSize at the END of instant id
--   W⁺  WSTORE(id): the tightest cWid  at the END of instant id
--
-- PROVENANCE per cell: `r` = pinned by `refl` below; everything else is
-- COMPILED (probe/Instant-Height-Main.agda, measured-not-rechecked), and
-- `—` is NOT MEASURED with the wall recorded under the table.  Rows 0 and
-- 1 of the compiled harness reproduce Charge-Probe's pinned cJ (23 and
-- 47) through this probe's pair-carrying walk, which is what licenses
-- the rest.
--
-- ══════════════════════════════════════════════════════════════════
-- A.  THE DEEPENING SCAN, progDT — insD₂ (two arrivals)
--
--   id    V    J    F    D     S       W      S⁺      W⁺
--    0    1   23    2    1    20       1      24       6
--    1    1   23    2    1    24       6      45    3072
--
-- B.  THE SAME, insD⁴ (four arrivals).  id 0 and 1 reproduce A exactly,
--     so the extra script length does not move the early instants
--
--   id    V    J    F    D     S       W      S⁺      W⁺
--    0    1   23    2    1    20       1      24       6
--    1    1   23    2    1    24       6      45    3072
--    2    1   23    2    1    45    3072     885   ⟨932 digits⟩
--    3    1   23    —    —   885  ⟨932d⟩       —       —
--
--   NOT MEASURED at id 3: F, D (mFolds/mJ build the real emit stream and
--   died out of memory at 8 GB in 23 s), S⁺ and W⁺ (W⁺(3) is a numeral
--   with about 10^931 digits and no harness reaches it).  V and J at
--   id 3 ARE measured — the mirror walk never materialises the burst —
--   and they are still 1 and 23.
--
-- C.  A SCAN DOWNSTREAM OF THE AMPLIFIER, progW — insD₂ and insD⁴
--     (identical on every measured cell)
--
--   id    V    J    F    D     S       W      S⁺      W⁺
--    0    2   47    4    1    20       1      87       9
--    1    6   91    —    —    87       9       —       —
--
--   NOT MEASURED at id 1: F, D, S⁺, W⁺ — every one of them re-runs the
--   real cascade, and all four ran past 120 s and were killed (this is
--   the same wall Charge-Probe recorded: "progW cascade 1 ran past five
--   minutes without normalising", now confirmed against the COMPILED
--   backend, so it is not a typechecker artefact).  id 2 and id 3: NOT
--   MEASURED, every column, killed at 120 s.
--
-- D.  THE TRIPLING SCAN over one shared level, pF1 — insG
--
--   id    V    J    F    D     S       W      S⁺      W⁺
--    0    1   28    6    4    10       1      87       9
--    1    1   28    6    4    87       9     843      81
--    2    1   28    6    4   843      81    7647     729
--    3    1   28    —    —  7647     729       —       —
--
--   NOT MEASURED at id 3: F, D, S⁺, W⁺ (killed at 120 s).  V and J are
--   measured and unmoved.
--
-- E.  THE TRIPLING SCAN over two shared levels, pF2 — insG²
--
--   id    V    J    F    D     S       W      S⁺      W⁺
--    0    1   58   14   10    10       1     843      81
--    1    1   58    —    —   843      81       —       —
--    2    —    —    —    —     —       —       —       —
--    3    —    —    —    —     —       —       —       —
--
--   NOT MEASURED: everything at id 2 and id 3, and F / D / S⁺ / W⁺ at
--   id 1 — all killed at 120 s.
--
-- F.  THE μ TICKER under the tripling wrap, pμ2 — NO SCRIPT AT ALL.
--     The one family with a clean four-instant sweep on every column
--
--   id    V    J    F    D     S       W      S⁺      W⁺
--    0    1   15    4    1    24       3      87       9
--    1    1   17    6    1    87       9     276      27
--    2    1   19    8    1   276      27     843      81
--    3    1   21   10    1   843      81    2544     243
--
-- G.  THE μ TICKER under the DEEPENING scan, pμD
--
--   id    V    J    F    D     S       W      S⁺      W⁺
--    0    1   25    4    1    24       6      45    3072
--    1    1   27    6    1    45    3072     885   ⟨932 digits⟩
--    2    1   29    —    —   885  ⟨932d⟩       —       —
--    3    —    —    —    —     —       —       —       —
--
--   NOT MEASURED at id 2: F, D, S⁺, W⁺ (out of memory at 8 GB in 23 s);
--   at id 3: everything (out of memory in 27 s).
--
--   W⁺(1) here is the SAME 932-digit numeral as progDT insD⁴'s W⁺(2).
--
-- H.  THE MINT LADDER, pL² 2 — insG², for contrast
--
--   id    V    J    F     D     S     W    S⁺    W⁺
--    0    1  205   51    21    18     1    18   144
--    1    1  969  495   153    18   144    18   144
--    2    1 3045 2059   637    18   144    18   144
--    3    1 7201 5511  1729    18   144    18   144
--
-- I.  ONE RUNG OF THE THREE-LEVEL LADDER, pL³ 0 — insG³ (two arrivals)
--
--   id    V    J    F     D     S     W    S⁺    W⁺
--    0    1   82   58    50     3     1     2     8
--    1    1  146  122   114     2     8     1     8
--
-- J.  THE CONTROL WITH NO ARRIVALS, progD — ins₀
--
--   id    V    J    F     D     S     W    S⁺    W⁺
--    0    0    0    0     0    45  3072    45  3072
--
--   Charge-Probe's finding (4) in its own currency: the whole deepening
--   happens inside the ROOT SUBSCRIBE FRAME.  The store is already at
--   size 45 and width 3072 before instant 0 begins, and instant 0 does
--   nothing at all
-- ══════════════════════════════════════════════════════════════════
--
-- THE FOUR RATIOS, tabulated off exactly those rows.  Nothing is read
-- off them here; the trends are the design session's.
--
-- (e1)  V(id)  vs  W(id) = WSTORE(id ∸ 1)
--
--   Every measured row fits EXCEPT ONE:
--
--     **progW at id 0: V = 2 against W = 1.**
--
--   progW at id 1 fits (V = 6 against W = 9), and every other row of
--   every other family has V = 1 against a W of 1 or more.  The breach
--   is the one Charge-Probe already located structurally: the burst the
--   inner mergeAll unwraps is produced INSIDE the same cascade, so the
--   frame reads a width the entry state does not have yet.  Whether it
--   recurs past id 0 is NOT MEASURED — progW's later instants are the
--   rows this container cannot reach.
--
-- (e2)  W⁺(id)  vs  story (W(id)) = 2 ^ (W + 1) ∸ 2
--       — Frame-Work-Probe's per-arrival law, i.e. ONE story per instant
--
--   family / id      W        W⁺           story W        verdict
--   progDT  0        1         6                 2        **BREACH** 3.0×
--   progDT  1        6      3072               126        **BREACH** 24.4×
--   progDT  2     3072  ⟨932d⟩       ⟨926 digits⟩          **BREACH** 4.7e6×
--   progW   0        1         9                 2        **BREACH** 4.5×
--   pF1     0        1         9                 2        **BREACH** 4.5×
--   pF1     1        9        81              1022        fits
--   pF1     2       81       729       2 ^ 82 ∸ 2         fits
--   pF2     0        1        81                 2        **BREACH** 40×
--   pμ2     0        3         9                14        fits
--   pμ2     1        9        27              1022        fits
--   pμ2     2       27        81      268435454           fits
--   pμ2     3       81       243       2 ^ 82 ∸ 2         fits
--   pμD     0        6      3072               126        **BREACH** 24.4×
--   pμD     1     3072  ⟨932d⟩       ⟨926 digits⟩          **BREACH** 4.7e6×
--   pL² 2   0        1       144                 2        **BREACH** 72×
--   pL² 2   1      144       144     2 ^ 145 ∸ 2          fits
--   pL³ 0   0        1         8                 2        **BREACH** 4×
--   pL³ 0   1        8         8               510        fits
--   progD   0     3072      3072     2 ^ 3073 ∸ 2         fits
--
--   **REAL WIDTH CLIMBS MORE THAN ONE STORY PER INSTANT.**  It does so
--   at id 0 on six of the nine families — where W = 1 and any real work
--   beats `story 1 = 2` — AND, on the two DEEPENING families, at id 1
--   and id 2 as well, where the entry width is already 6 and 3072.
--   progDT id 2 and pμD id 1 are the sharp ones: a 932-digit W⁺ against
--   a 926-digit `2 ^ (W + 1) ∸ 2`, a factor of 4721664.  The climb is
--   sustained, not a base artefact.
--
--   IN THE CAPS' OWN CURRENCY IT IS STILL ONE PASS.  `foldStep S w =
--   S ^ suc w` is not `2 ^ suc w`: its base is cSize, and at the
--   measured S every single row above needs exactly ONE foldStep pass
--   (`wNeed`), including progDT id 2, where foldStep 45 3072 = 45 ^ 3073
--   is a 5081-digit numeral against a 932-digit W⁺.  So "more than one
--   story" is a statement about the base-2 law and NOT about the
--   recurrence the caps actually iterate
--
-- (e3)  J(id)  vs  jForm D S V = D * S * suc (V * suc S)
--       — the receipt-dictated charge with the MEASURED V
--
--   family / id       J     jForm      J/jForm
--   progDT  0        23       440       0.0523
--   progDT  1        23       624       0.0369
--   progDT  2        23      2115       0.0109
--   progW   0        47       860       0.0547
--   pF1     0        28       480       0.0583
--   pF1     1        28     30972       0.0009
--   pF1     2        28   2849340       0.00001
--   pF2     0        58      1200       0.0483
--   pμ2     0        15       624       0.0240
--   pμ2     1        17      7743       0.0022
--   pμ2     2        19     76728       0.0002
--   pμ2     3        21    712335       0.00003
--   pμD     0        25       624       0.0401
--   pμD     1        27      2115       0.0128
--   pL² 2   0       205      7560       0.0271
--   pL² 2   1       969     55080       0.0176
--   pL² 2   2      3045    229320       0.0133
--   pL² 2   3      7201    622440       0.0116
--   pL³ 0   0        82       750       0.1093
--   pL³ 0   1       146       912       0.1601
--   progD   0         0         0       —  (0 ≤ 0)
--
--   Every measured row FITS, worst ratio 0.16 (pL³ 0 at id 1).  Rows
--   where D is NOT MEASURED are absent rather than assumed: progDT id 3,
--   progW id 1, pF1 id 3, pF2 id 1 and pμD id 2 all have J and V and S
--   but no D, and jForm is linear in D, so nothing is claimed for them.
--
-- (e4)  S⁺(id)  vs  one iterSize pass sequence at base S
--
--   Reported as `sNeed S S⁺ S`, the MINIMAL number of sizeStep passes
--   that reaches S⁺ from S, against the count the charge form allows
--   (jForm, the same number as column `jForm` above):
--
--   family / id     S       S⁺     sNeed     allowed
--   progDT  0      20       24         1         440
--   progDT  1      24       45         1         624
--   progDT  2      45      885         1        2115
--   progW   0      20       87         1         860
--   pF1     0      10       87         1         480
--   pF1     1      87      843         1       30972
--   pF1     2     843     7647         1     2849340
--   pF2     0      10      843         2        1200
--   pμ2     0      24       87         1         624
--   pμ2     1      87      276         1        7743
--   pμ2     2     276      843         1       76728
--   pμ2     3     843     2544         1      712335
--   pμD     0      24       45         1         624
--   pμD     1      45      885         1        2115
--   pL² 2   0      18       18         0        7560
--   pL² 2   1      18       18         0       55080
--   pL³ 0   0       3        2         0         750
--   pL³ 0   1       2        1         0         912
--   progD   0      45       45         0           0
--
--   The size axis needs 0, 1 or 2 passes on every row measured, against
--   allowances in the hundreds to millions.  pF2 at id 0 is the only
--   two-pass row.
--
-- ══════════════════════════════════════════════════════════════════
-- WHAT THE FAMILIES DO TO EACH AXIS, as rows and not as a trend:
--
--   · pμ2 is the only family with all four instants on every column.
--     Its width goes 3, 9, 27, 81, 243 — ×3 per instant — its size 24,
--     87, 276, 843, 2544 — ×3 per instant — while V stays 1, D stays 1
--     and J moves by exactly 2 per instant (15, 17, 19, 21).
--   · pL² 2 is the opposite corner: S and W are FLAT at 18 and 144 for
--     all four instants while D goes 21, 153, 637, 1729 and J goes 205,
--     969, 3045, 7201.  The ladder buys COUNT, not axes.
--   · the deepening families buy neither count nor size but WIDTH: J is
--     23 at every instant of progDT and 25, 27, 29 on pμD, D is 1, and
--     W goes 1, 6, 3072, 10^931.
--   · progW is the only family where V ever exceeds 1 (2 and 6), and the
--     only one where V has ever exceeded W
------------------------------------------------------------------

------------------------------------------------------------------
-- THE PINS.  Everything below is `refl` against the real evaluator or
-- numeral arithmetic on a row already pinned.  The DEEP cells are not
-- here — they are the compiled table above — and the numeral gates are
-- written on the pinned numerals so a gate costs no evaluator run
------------------------------------------------------------------

-- (0) CALIBRATION: the pair-carrying walk reproduces Charge-Probe's cJ
_ : iJ 0 progDT insD₁ ≡ 23
_ = refl

_ : iJ 0 progW insD₂ ≡ 47
_ = refl

-- (1) THE (e1) BREACH, both sides pinned.  Charge-Probe pins
-- `mW 0 progW insD₂ ≡ 1`; here is the V that beats it
_ : iV 0 progW insD₂ ≡ 2
_ = refl

_ : (2 ≤ᵇ 1) ≡ false
_ = refl

-- and the row that does NOT breach, so the breach is read as a corner
_ : iV 0 progDT insD₁ ≡ 1
_ = refl

-- (2) A WHOLE INSTANT ROW, pinned: the μ ticker at id 0, which is the
-- family with the clean sweep
_ : tup 0 pμ2 ins₀ ≡ 1 ∷ 15 ∷ 4 ∷ 1 ∷ 24 ∷ 3 ∷ 87 ∷ []
_ = refl

_ : wStore 0 pμ2 ins₀ ≡ 9
_ = refl

-- and the ladder's, which is the opposite corner
_ : tup 0 (pL³ 0) insG³ ≡ 1 ∷ 82 ∷ 58 ∷ 50 ∷ 3 ∷ 1 ∷ 2 ∷ []
_ = refl

-- (3) THE CONTROL: progD's whole run happens in the root subscribe
-- frame, so instant 0 is empty and the store is ALREADY at width 3072
_ : tup 0 progD ins₀ ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 45 ∷ 3072 ∷ 45 ∷ []
_ = refl

------------------------------------------------------------------
-- (4) THE (e2) GATES, as numeral arithmetic on the compiled rows.
-- `story` is Frame-Work-Probe's law; a `false` here is a width climbing
-- MORE than one story in one instant
------------------------------------------------------------------

_ : story 1 ≡ 2
_ = refl

_ : story 6 ≡ 126
_ = refl

-- progDT / pμD id 0: 6 against 2
_ : (6 ≤ᵇ story 1) ≡ false
_ = refl

-- progDT id 1 and pμD id 0: 3072 against 126
_ : (3072 ≤ᵇ story 6) ≡ false
_ = refl

-- progW id 0 and pF1 id 0: 9 against 2
_ : (9 ≤ᵇ story 1) ≡ false
_ = refl

-- pF2 id 0: 81 against 2
_ : (81 ≤ᵇ story 1) ≡ false
_ = refl

-- pL² 2 id 0: 144 against 2
_ : (144 ≤ᵇ story 1) ≡ false
_ = refl

-- pL³ 0 id 0: 8 against 2
_ : (8 ≤ᵇ story 1) ≡ false
_ = refl

-- AND THE SUSTAINED ONE, at the only rung where the entry width is
-- already large: W = 3072, and `story 3072` is a 926-digit numeral where
-- the measured W⁺ has 932.  The denominator's digit count is pinned
-- here; the numerator's is the compiled row `WDG progDT insD4 id2 = 932`
_ : digitsGo 1000000 (story 3072) ≡ 926
_ = refl

-- the rows that FIT, so the breach is not read as universal
_ : (81 ≤ᵇ story 9) ≡ true
_ = refl

_ : (243 ≤ᵇ story 81) ≡ true
_ = refl

_ : (144 ≤ᵇ story 144) ≡ true
_ = refl

_ : (9 ≤ᵇ story 3) ≡ true
_ = refl

------------------------------------------------------------------
-- (5) AND THE SAME CLIMBS IN THE CAPS' OWN CURRENCY, `foldStep S w =
-- S ^ suc w`.  ONE pass covers every measured row, including the two
-- that breach the base-2 story by a factor of 4.7 million
------------------------------------------------------------------

_ : wNeed 20 6 1 ≡ 1
_ = refl

_ : wNeed 24 3072 6 ≡ 1
_ = refl

_ : wNeed 10 81 1 ≡ 1
_ = refl

_ : wNeed 18 144 1 ≡ 1
_ = refl

_ : wNeed 843 243 81 ≡ 1
_ = refl

-- progDT id 2: foldStep 45 3072 is a 5081-digit numeral against a
-- 932-digit W⁺, so one pass covers it with 4000 digits to spare
_ : digitsGo 1000000 (foldStep 45 3072) ≡ 5081
_ = refl

------------------------------------------------------------------
-- (6) THE (e3) GATES: the receipt-dictated charge with the MEASURED V,
-- read on the pinned numerals.  Every measured row fits
------------------------------------------------------------------

_ : jForm 1 20 1 ≡ 440
_ = refl

_ : jForm 1 20 2 ≡ 860
_ = refl

_ : (23 ≤ᵇ jForm 1 20 1) ≡ true
_ = refl

_ : (47 ≤ᵇ jForm 1 20 2) ≡ true
_ = refl

_ : (28 ≤ᵇ jForm 4 10 1) ≡ true
_ = refl

_ : (58 ≤ᵇ jForm 10 10 1) ≡ true
_ = refl

_ : (15 ≤ᵇ jForm 1 24 1) ≡ true
_ = refl

_ : (21 ≤ᵇ jForm 1 843 1) ≡ true
_ = refl

_ : (25 ≤ᵇ jForm 1 24 1) ≡ true
_ = refl

-- the mint ladder, where D is what moves
_ : (205 ≤ᵇ jForm 21 18 1) ≡ true
_ = refl

_ : (7201 ≤ᵇ jForm 1729 18 1) ≡ true
_ = refl

-- and the WORST ratio in the table, 0.16
_ : (146 ≤ᵇ jForm 114 2 1) ≡ true
_ = refl

_ : jForm 114 2 1 ≡ 912
_ = refl

------------------------------------------------------------------
-- (7) THE (e4) GATES: the minimal sizeStep pass count against the count
-- the same form allows.  0, 1 or 2 everywhere
------------------------------------------------------------------

_ : sNeed 20 24 20 ≡ 1
_ = refl

_ : sNeed 24 45 24 ≡ 1
_ = refl

_ : sNeed 45 885 45 ≡ 1
_ = refl

_ : sNeed 843 7647 843 ≡ 1
_ = refl

-- the only two-pass row
_ : sNeed 10 843 10 ≡ 2
_ = refl

-- and the ladder, whose size axis does not move at all
_ : sNeed 18 18 18 ≡ 0
_ = refl

_ : (1 ≤ᵇ jForm 1 20 1) ≡ true
_ = refl

_ : (2 ≤ᵇ jForm 10 10 1) ≡ true
_ = refl
