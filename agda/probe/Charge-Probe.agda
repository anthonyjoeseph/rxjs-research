-- ROADMAP: INFRASTRUCTURE — program families for Instant-Height-Probe/-Main and Nest-Count-Probe/-Main.
-- DELETE WHEN: its last dependent probe is deleted  [T8]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
------------------------------------------------------------------
-- THE CHARGE PROBE: does one cascade's j fit `D * cSize`?
--
-- `cascadeGo-charge` is the half of the budget claim that survived the
-- delivery bound's third correction untouched, and it is now the
-- suspect one.  It says `j ≤ D * cSize` — one delivery's frames times a
-- per-frame charge of cSize.  But the receipt `stepFrame-caps` actually
-- reports for a scan frame is
--
--     j′ = suc (length vals * suc (sizeᵗ fn))
--
-- ONE FOLD PER NODE OF THE STEP FUNCTION, PER PAYLOAD — and
-- `length vals` is a BURST WIDTH, which nothing entry-readable bounds.
-- It cannot be paid by cWid (Width-Count-Probe: a count reading cWid
-- iterates the tower function once per instant, which destroys
-- capsAt-tower's linear height and caps-fuel-root with it), and it
-- cannot be paid by an entry width (Frame-Work-Probe: a frame's
-- payload count climbs the width ladder across arrivals, 2 ↦ 8).
--
-- SO THE QUESTION IS WHETHER THE WIDTH FACTOR IS ABSORBED IN PRACTICE.
-- `D * cSize` is generous in two ways the receipt is not: D counts
-- deliveries whose paths are `root` or `share-sink` and cost NOTHING,
-- and cSize is the tightest cap the whole state admits, which on a
-- width-heavy program is far above any single step function's size.
-- This probe measures the receipt-weighted j directly and gates it.
--
-- WHAT IS MEASURED, and how it relates to the conjunct's own j:
--
--   cJ   the RECEIPT-WEIGHTED j: one summand per `↠` frame, weighted by
--        the receipt stepFrame-caps reports for that frame — `suc sizeᵗ`
--        at map-f, `suc (length vals * suc sizeᵗ)` at scan-f, 0 at
--        take-f, and 1 at the two *All edges (which delegate to
--        subscribeE and whose j is not locally readable).  It is a
--        LOWER BOUND on the conjunct's j: the *All edges under-count,
--        and pushBurst's per-emit re-entry is not counted at all.  So a
--        row that BREAKS the budget breaks it for real; a row that fits
--        is evidence and not a proof.
--   cJ1  the same walk counting ONE per frame — Mint-Loop-Shapes' `mJ`
--        re-derived here, so the weighting can be read off as a ratio
--        rather than guessed.
--   D    deliveries, off the evaluator's own ledger (`mFolds`).
--   S    the tightest cSize the pre-state admits (`mS`).
--   R    the entry registry's length (`mReg`), i.e. the tightest cReg.
--   W    the tightest cWid the pre-state admits (`mW`) — `pWᵛ` of every
--        stored accumulator and live pending, `pWᵉ` of every queued
--        concat inner, read off the same state `mS` is read off.
--
-- and the gates are `cJ ≤ D * S` (the conjunct as stated),
-- `cJ ≤ 2 ^ (2 ^ R) * S` (the count `frameBlowup` now spends), and —
-- added 2026-08-01, §(f) and §(g) below — the two REPAIRS:
-- `cJ ≤ D * S * suc W`, the design session's width-factor ruling, which
-- progW STILL BREAKS (47 against 40); and
-- `cJ ≤ D * S * suc (W * suc S)`, the form the receipt table itself
-- dictates, which every row fits (47 against 440).
--
-- THE FAMILIES ARE THE WIDTH-HEAVY ONES, chosen because they are where
-- the `length vals` factor is largest:
--
--   · the DEEPENING SCAN (Frame-Work-Probe's deepScan) — an obs-typed
--     accumulator that re-wraps itself and is unwrapped by a *All, the
--     sharpest known width amplifier, on the recurrence
--     wₖ₊₁ = 2 ^ (wₖ + 1) − 2;
--   · the TRIPLING scan (Fold-Count-Probe's wrap3) — three occurrences
--     of the accumulator per fold, over the share ladders;
--   · the MINT LADDERS at their deepest measurable k, where D is
--     largest.
--
-- Standalone, so src/Main.agda never reaches it.  It shares
-- Mint-Loop-Shapes' harness (runSt / stAt / mS / mReg / mFolds / mJ) and
-- its ladders; the width-heavy programs are rebuilt here because their
-- home probes are the two slowest in the tree.
------------------------------------------------------------------
module Charge-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _≤ᵇ_; _⊔_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.List using (List; []; _∷_; _++_; length; map; any; foldr)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin; toℕ) renaming (zero to fz; suc to fsuc)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; Tick; Gas; after_,_; hot)
open import Rx.Exp  using (Ctx; Closed; Exp; Tm; Fn; Val; natᵗ; obs; _×ᵗ_;
                           input; ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; nat̂;
                           fstᵗ; varᵗ; sizeᵗ)
open import Rx.Frame-Width using (pWᵉ; pWᵛ)
open import Rx.Evaluator using (Slots; scripted; Sched; EvalSt;
                                sched-next; budgetAt; LiveSource;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                root; Path; share-sink; _↠_;
                                Frame; map-f; scan-f; take-f;
                                from-inner; thru-outer;
                                RegId; Arrival; arrTy; arrVal; arrTick;
                                stepFrame; shareAdmit; shareLatch; shareFinish;
                                chainsOf; cascadeLatch)

open import Mint-Loop-Shapes
  using (runSt; stAt; mS; mReg; mFolds; mJ;
         accV; seedO;
         Γˢ¹; insG; Γˢ²; insG²; Γˢ³; insG³; Γˢ⁴; insG⁴;
         pL²; pL³; pL⁴)

------------------------------------------------------------------
-- THE RECEIPT TABLE, transcribed from stepFrame-caps clause for clause.
--
--   map-f       mapFrame-caps       j′ = suc (sizeᵗ fn)
--   scan-f      scanFrame-caps      j′ = suc (length vals * suc (sizeᵗ fn))
--   take-f      takeDispatch-caps   j′ = 0
--   from-inner  innerReact-caps     j′ = the sub-walk's — not local
--   thru-outer  thruWalk-caps       j′ = the sub-walk's — not local
--
-- The last two are counted as ONE, which is why cJ is a lower bound
------------------------------------------------------------------

frameJ : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → List (Val Γ s) → ℕ
frameJ (map-f fn)         vals = suc (sizeᵗ fn)
frameJ (scan-f fn _)      vals = suc (length vals * suc (sizeᵗ fn))
frameJ (take-f _)         vals = 0
frameJ (from-inner _ _ _) vals = 1
frameJ (thru-outer _ _)   vals = 1

------------------------------------------------------------------
-- THE WEIGHTED MIRROR, Mint-Loop-Shapes' `fpFolds` with the summand at
-- the `↠` clause read off the table above instead of being 1.  It calls
-- the REAL stepFrame / shareAdmit / shareLatch / shareFinish, so the
-- state it walks is the state the evaluator walks, and it threads the
-- delivery ledger the same way so `cJdel` can check it against mFolds.
------------------------------------------------------------------

wfp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    → Gas → ℕ → Id → Tick
    → Path Γ u t → List (Val Γ u) → Bool
    → Sched Γ → EvalSt e → ℕ × Sched Γ × EvalSt e

wds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Gas → ℕ → Id → Tick → (i : Fin n)
    → List (Val Γ (Data.Vec.lookup Γ i)) → Bool
    → Sched Γ → EvalSt e → ℕ × Sched Γ × EvalSt e

wsg : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Gas → ℕ → Id → Tick → (i : Fin n)
    → List (Val Γ (Data.Vec.lookup Γ i)) → Bool
    → List (RegId × Path Γ (Data.Vec.lookup Γ i) t)
    → Sched Γ → EvalSt e → ℕ × Sched Γ × EvalSt e

wfp sf gas id now root vals fin sched st = 0 , sched , st
wfp sf gas id now (share-sink i) vals fin sched st =
  wds sf gas id now i vals fin sched st
wfp sf gas id now (f ↠ p) vals fin sched st =
  let (vals′ , _ , fin′ , sched₁ , st₁) = stepFrame sf id now f p vals fin sched st
      (m , sched₂ , st₂) = wfp sf gas id now p vals′ fin′ sched₁ st₁
  in frameJ f vals + m , sched₂ , st₂

wds sf zero    id now i vals fin sched st = 0 , sched , st
wds sf (suc gas) id now i vals fin sched st =
  let (m , sched₁ , st₁) =
        wsg sf gas id now i vals fin
          (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)
      (_ , sched₂ , st₂) = shareFinish i fin ([] , sched₁ , st₁)
  in m , sched₂ , st₂

wsg sf gas id now i vals fin []               sched st = 0 , sched , st
wsg sf gas id now i vals fin ((rid , p) ∷ ps) sched st
  with any (Data.Nat._≡ᵇ_ rid) (EvalSt.cancelled st)
... | true  = wsg sf gas id now i vals fin ps sched st
... | false =
  let (m₁ , sched₁ , st₁) =
        wfp sf gas id now p vals fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
      (m₂ , sched₂ , st₂) = wsg sf gas id now i vals fin ps sched₁ st₁
  in m₁ + m₂ , sched₂ , st₂

wcs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → (a : Arrival Γ) → Id → List (RegId × Path Γ (arrTy a) t)
    → Sched Γ → EvalSt e → ℕ × Sched Γ × EvalSt e
wcs a id []                   sched st = 0 , sched , st
wcs {n = n} {e = e} a id ((rid , c) ∷ chains) sched st
  with any (Data.Nat._≡ᵇ_ rid) (EvalSt.cancelled st)
... | true  = wcs a id chains sched st
... | false =
  let (m₁ , sched₁ , st₁) =
        wfp (budgetAt e (Sched.slots sched) id) n id (arrTick a) c
            (arrVal a ∷ []) (Arrival.isLast a) sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
      (m₂ , sched₂ , st₂) = wcs a id chains sched₁ st₁
  in m₁ + m₂ , sched₂ , st₂

wAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
    → ℕ × EvalSt e
wAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = 0 , st
...   | inj₂ (a , sched′) =
        let (m , _ , st′) = wcs a nid (chainsOf a st) sched′ (cascadeLatch a st)
        in m , st′

-- the receipt-weighted j of ONE cascade
cJ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
cJ fuel e ins = proj₁ (wAt fuel e ins)

-- and the same walk's delivery ledger, so the mirror can be checked
-- against the evaluator proper
cJdel : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
cJdel fuel e ins = length (EvalSt.delivered (proj₂ (wAt fuel e ins)))

------------------------------------------------------------------
-- THE WIDTH-HEAVY PROGRAMS.
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

insD₁ insD₂ : Slots Γ₁
insD₁ fz = scripted (hot ((after 0 , 1) ∷ []))
insD₂ fz = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

-- THE DEEPENING SCAN, Frame-Work-Probe's: the plug lands in an inner
-- scan's SOURCE, so every fold re-wraps the accumulator one level
-- deeper and the *All unwraps it — the sharpest width amplifier known
deepScan : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepScan = strmᵗ (mergeAllᵉ (scanᵉ (strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ []))))
                                   seedO
                                   (mergeAllᵉ (ofᵉ (accV ∷ [])))))

progD : Closed Γ₀ natᵗ
progD = mergeAllᵉ (scanᵉ deepScan seedO (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])))

progDT : Closed Γ₁ natᵗ
progDT = mergeAllᵉ (scanᵉ deepScan seedO (input fz))

-- THE TRIPLING SCAN, Fold-Count-Probe's wrap3: three occurrences of the
-- accumulator, so every fold triples the stored width
wrap3 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap3 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ accV ∷ [])))

pF1 : Closed Γˢ¹ natᵗ
pF1 = mergeAllᵉ (scanᵉ wrap3 seedO (input fz))

pF2 : Closed Γˢ² natᵗ
pF2 = mergeAllᵉ (scanᵉ wrap3 seedO (input fz))

-- A SCAN DOWNSTREAM OF THE AMPLIFIER, which is where `length vals` can
-- exceed one inside the cascade walk: the inner mergeAll unwraps the
-- deepening accumulator and the outer scan-f frame receives the whole
-- burst as ONE payload list
progW : Closed Γ₁ natᵗ
progW = mergeAllᵉ (scanᵉ wrap3 seedO (mergeAllᵉ (scanᵉ deepScan seedO (input fz))))

------------------------------------------------------------------
-- THE ROWS.  Every one `refl`-checked against the real evaluator, and
-- every gate is the conjunct's own inequality at the TIGHTEST caps the
-- pre-state admits — which is the only honest denominator: `c` in
-- `cascadeGo-charge` has to satisfy `capsOK? c sched st`, so cSize c is
-- at least mS, and a breach at mS is a breach at the tight admissible
-- level.
--
--   program        slots   casc    cJ   mJ     D    S   D*S    verdict
--   progDT         insD₁     0     23    2     1   20    20    BREACH  1.15
--   progDT         insD₂     0     23    2     1   20    20    BREACH  1.15
--   progDT         insD₂     1     23    2     1   24    24    fits
--   progW          insD₂     0     47    4     1   20    20    BREACH  2.35
--   pF1            insG      0     28    6     4   10    40    fits
--   pF1            insG      1     28    6     4   87   348    fits
--   pF2            insG²     0     58   14    10   10   100    fits
--   pL² 0          insG²     0     32   20    16    3    48    fits
--   pL³ 0          insG³     0     82   58    50    3   150    fits
--   pL³ 1          insG³     0    398  226   106   10  1060    fits
--
-- NOT MEASURABLE at this container: progW cascade 1 and pF2 cascade 1
-- both ran past five minutes without normalising.  progW's cascade 1 is
-- the row that would say whether the breach ratio CLIMBS with the
-- deepening, and it is the one row this probe most wants.
--
-- THE READING, and it has two parts that should not be conflated.
--
-- (1) THE CONJUNCT IS FALSE, AND IT IS FALSE WITHOUT ANY WIDTH AT ALL.
-- progDT's cascade delivers ONCE along a two-frame chain, and the
-- receipt for the scan frame alone is `suc (1 * suc (sizeᵗ deepScan))`
-- = sizeᵗ deepScan + 2, with sizeᵗ deepScan = 20 = mS exactly.  So
-- `j ≤ D * cSize` is short by the receipt's own two `suc`s before the
-- payload count is even 2.  `D * cSize` charges cSize per delivery
-- where the receipt charges `1 + V * (1 + N)`, and at V = 1, N = cSize
-- that is cSize + 2.  Any single-delivery cascade whose chain carries a
-- scan frame at the cap breaks it.
--
-- (2) AND THE WIDTH FACTOR IS REAL ON TOP OF THAT.  progW puts a second
-- scan DOWNSTREAM of the amplifier — the inner mergeAll unwraps the
-- deepening accumulator, so the outer scan-f frame receives the whole
-- burst as one payload list — and the same one-delivery cascade costs
-- 47 against the same budget of 20.  The two frames' receipts are
-- 22 and 24: the second one is `suc (V * suc (sizeᵗ wrap3))` with V the
-- unwrapped burst width, and it is the larger of the two even though
-- wrap3 is a THIRD the size of deepScan.
--
-- (3) THE LADDERS ARE NOT WHERE THE PROBLEM IS.  Every mint-ladder and
-- share-ladder row fits, with ratios 0.67, 0.55, 0.38 — because their
-- deliveries are many and each carries ONE payload, so `D * cSize`
-- grows with D while the receipt does not.  The families that break it
-- are the ones with FEW deliveries and WIDE payloads, which is the
-- opposite corner from the one every previous count refutation came
-- from.
--
-- (4) AND THE SHARPEST AMPLIFIER NEVER ENTERS A CASCADE AT ALL.  progD
-- — Frame-Work-Probe's own deepScan program, over a synchronous `ofᵉ`
-- source — has NO arrivals: its whole run happens inside the root
-- subscribe frame.  So the deepening scan's width is charged to
-- `subscribeE`, not to `cascadeGo`, and it lands on GAP 4's missing
-- companion (a), the subscribe-level charge, rather than on this
-- conjunct.  That is recorded here because it is the reason a probe
-- aimed at cascadeGo-charge cannot see the worst case
------------------------------------------------------------------

-- (a) THE BREACHES.  `cJ` is a LOWER bound on the conjunct's j, so
-- these refute `j ≤ D * cSize` outright
_ : (cJ 0 progDT insD₁ ≤ᵇ mFolds 0 progDT insD₁ * mS 0 progDT insD₁) ≡ false
_ = refl

_ : cJ 0 progDT insD₁ ≡ 23
_ = refl

_ : mFolds 0 progDT insD₁ * mS 0 progDT insD₁ ≡ 20
_ = refl

_ : (cJ 0 progW insD₂ ≤ᵇ mFolds 0 progW insD₂ * mS 0 progW insD₂) ≡ false
_ = refl

_ : cJ 0 progW insD₂ ≡ 47
_ = refl

_ : mFolds 0 progW insD₂ * mS 0 progW insD₂ ≡ 20
_ = refl

-- (b) THE ROWS THAT FIT, so the breach is read as a corner and not as a
-- collapse
_ : (cJ 1 progDT insD₂ ≤ᵇ mFolds 1 progDT insD₂ * mS 1 progDT insD₂) ≡ true
_ = refl

_ : (cJ 0 pF1 insG ≤ᵇ mFolds 0 pF1 insG * mS 0 pF1 insG) ≡ true
_ = refl

_ : (cJ 0 pF2 insG² ≤ᵇ mFolds 0 pF2 insG² * mS 0 pF2 insG²) ≡ true
_ = refl

_ : (cJ 0 (pL² 0) insG² ≤ᵇ mFolds 0 (pL² 0) insG² * mS 0 (pL² 0) insG²) ≡ true
_ = refl

_ : (cJ 0 (pL³ 0) insG³ ≤ᵇ mFolds 0 (pL³ 0) insG³ * mS 0 (pL³ 0) insG³) ≡ true
_ = refl

_ : (cJ 0 (pL³ 1) insG³ ≤ᵇ mFolds 0 (pL³ 1) insG³ * mS 0 (pL³ 1) insG³) ≡ true
_ = refl

-- (c) THE COUNT frameBlowup ACTUALLY SPENDS, `D̂ c * cSize c`, covers
-- every row including the breaches — by an astronomical margin, since
-- D̂ is a 2-tower.  So the repair the charge needs is not more count; it
-- is a charge face that reads the width
_ : (47 ≤ᵇ 2 ^ (2 ^ 1) * 20) ≡ true
_ = refl

_ : (398 ≤ᵇ 2 ^ (2 ^ 7) * 10) ≡ true
_ = refl

-- (d) THE MIRROR IS FAITHFUL: its delivery ledger is the evaluator's
_ : cJdel 0 progW insD₂ ≡ mFolds 0 progW insD₂
_ = refl

_ : cJdel 0 (pL³ 1) insG³ ≡ mFolds 0 (pL³ 1) insG³
_ = refl

-- (e) AND progD HAS NO CASCADE: the amplifier fires in the root
-- subscribe frame, so its width is subscribeE-charge's problem
_ : mFolds 0 progD ins₀ ≡ 0
_ = refl

------------------------------------------------------------------
-- THE NEW CHARGE FORM, GATED ON THE SAME ROWS (2026-08-01).
--
-- The conjunct this probe refuted is `j ≤ D * cSize`.  The repair the
-- design session ruled is `j ≤ D * cSize * suc cWid` — the width factor
-- the receipts actually pay for, since `scanFrame-caps` charges
-- `suc (length vals * suc (sizeᵗ fn))` and `length vals` is a burst
-- width.  So the gate has to be re-run at the tight admissible cWid,
-- exactly as the old one was run at the tight admissible cSize.
--
-- `mW` is that denominator: the largest frame width `capsOK?` bounds in
-- the PRE-CASCADE state — `pWᵛ` of every stored accumulator and every
-- live pending, `pWᵉ` of every queued concat inner — read off the same
-- state `mS` is read off.  A row that fits at mW fits at every
-- admissible cWid, because capsOK? forces cWid ≥ mW.
------------------------------------------------------------------

nodeW : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → NodeState Γ → ℕ
nodeW j sl (scan-st {t} v)   = pWᵛ j sl t v
nodeW j sl (concat-st q _ _) = foldr (λ o m → pWᵉ j sl o ⊔ m) 0 q
nodeW j sl (take-st _)       = 0
nodeW j sl (merge-st _ _)    = 0
nodeW j sl (switch-st _ _)   = 0
nodeW j sl (exhaust-st _ _)  = 0

liveW : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → LiveSource Γ → ℕ
liveW j sl l = foldr (λ tv m → pWᵛ j sl (LiveSource.elemTy l) (proj₂ tv) ⊔ m) 0
                     (LiveSource.pending l)

-- the tightest cWid the pre-cascade state admits
mW : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mW {n = n} fuel e ins =
  let (sched , st) = stAt fuel e ins
  in foldr (λ kv m → nodeW n (Sched.slots sched) (proj₂ kv) ⊔ m) 0
           (EvalSt.nodes st)
     ⊔ foldr (λ l m → liveW n (Sched.slots sched) l ⊔ m) 0 (Sched.live sched)

-- THE TIGHT DENOMINATORS, measured.  Every one of these programs
-- carries width ONE in its pre-cascade state: the amplifier has not
-- folded yet at cascade 0, so `suc cWid` is a factor of TWO and no more
_ : mW 0 progDT insD₁ ≡ 1
_ = refl

_ : mW 0 progW insD₂ ≡ 1
_ = refl

_ : mW 0 pF1 insG ≡ 1
_ = refl

-- (f) THE RULING'S FORM, `j ≤ D * cSize * suc cWid`, IS STILL FALSE.
-- progDT now fits (23 against 40) — but progW does NOT: 47 against
-- 1 * 20 * 2 = 40.  The width factor the state can be charged for at
-- entry is `suc cWid` = 2, and the frame that costs the 47 reads a
-- width the state does not have YET: the burst the inner mergeAll
-- unwraps is produced INSIDE the same cascade.  So a charge linear in
-- the entry cWid does not reach it
_ : (cJ 0 progDT insD₁
       ≤ᵇ mFolds 0 progDT insD₁ * mS 0 progDT insD₁ * suc (mW 0 progDT insD₁))
      ≡ true
_ = refl

_ : (cJ 0 progW insD₂
       ≤ᵇ mFolds 0 progW insD₂ * mS 0 progW insD₂ * suc (mW 0 progW insD₂))
      ≡ false
_ = refl

_ : mFolds 0 progW insD₂ * mS 0 progW insD₂ * suc (mW 0 progW insD₂) ≡ 40
_ = refl

-- (g) THE FORM THE RECEIPT TABLE ITSELF DICTATES, and it covers every
-- row.  Read it off `frameJ` rather than guessed: one frame costs at
-- most `suc (length vals * suc (sizeᵗ fn))` ≤ `suc (cWid * suc cSize)`,
-- a delivery's chain carries at most `pathLen ≤ cSize` frames, and a
-- cascade makes at most D deliveries —
--
--     j ≤ D * cSize * suc (cWid * suc cSize)
--
-- which is the same product with the PER-FRAME receipt in place of the
-- bare width.  It is cubic in the caps where the refuted form was
-- linear, and that is exactly the difference between charging a frame
-- `cSize` and charging it its own receipt
_ : (cJ 0 progDT insD₁
       ≤ᵇ mFolds 0 progDT insD₁ * mS 0 progDT insD₁
          * suc (mW 0 progDT insD₁ * suc (mS 0 progDT insD₁)))
      ≡ true
_ = refl

_ : (cJ 0 progDT insD₂
       ≤ᵇ mFolds 0 progDT insD₂ * mS 0 progDT insD₂
          * suc (mW 0 progDT insD₂ * suc (mS 0 progDT insD₂)))
      ≡ true
_ = refl

_ : (cJ 0 progW insD₂
       ≤ᵇ mFolds 0 progW insD₂ * mS 0 progW insD₂
          * suc (mW 0 progW insD₂ * suc (mS 0 progW insD₂)))
      ≡ true
_ = refl

_ : (cJ 0 pF1 insG
       ≤ᵇ mFolds 0 pF1 insG * mS 0 pF1 insG
          * suc (mW 0 pF1 insG * suc (mS 0 pF1 insG)))
      ≡ true
_ = refl

-- the margins, so the form is not read as a blank cheque: progW's
-- breach of 47-against-20 becomes 47 against 440
_ : mFolds 0 progW insD₂ * mS 0 progW insD₂
      * suc (mW 0 progW insD₂ * suc (mS 0 progW insD₂)) ≡ 440
_ = refl
