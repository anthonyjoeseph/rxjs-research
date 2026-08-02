------------------------------------------------------------------
-- THE FRAME-MINT PROBE: what does ONE `stepFrame` mint, and how wide
-- is the burst it is handed?
--
-- THE TWO AXIOMS IT GATES.  `cascadeGo-deliveries` is proven
-- (.Caps-Face), on two frame-local postulates that charge at the
-- cascade's ENTRY caps:
--
--   stepFrame-entry-mint   one frame adds at most `cSize * suc cWid`
--                          registrations, at the ENTRY level
--   stepFrame-entry-caps   its second conjunct, `sf-vals`, says the
--                          payload list it hands the next frame is
--                          still inside `valsCaps? c sl` — whose width
--                          conjunct is `length vals ≤ suc cWid`
--
-- Both quantities are per FRAME, and no probe in the corpus measured
-- them: Mint-Loop-Frames reports mints and frames per CASCADE (9948
-- against 162666 frames at its deepest measurable rung), and an average
-- is not a maximum.  This probe reports the maxima.
--
-- HOW, AND WHY IT IS CHEAP.  Mint-Loop-Shapes' mirror walk already
-- exists and already calls the REAL `stepFrame`, `shareAdmit`,
-- `shareLatch` and `shareFinish` — so the state it walks is the state
-- the evaluator walks.  This file is that mirror again with the fold
-- count replaced by two maxima, read the same exact way the generation
-- stamp reads its mint window: off `EvalSt.nextReg` around the call,
-- which is exact because registrations mint ids in order and nothing
-- else moves the counter.
--
-- WHAT A ROW MEANS.  `fmMint` is a max over the frames of ONE cascade,
-- so a row that exceeds the budget breaks the axiom for real.  A row
-- that fits is evidence and not a proof — and the standing warning at
-- the head of Mint-Loop-Probe applies with full force: this family's
-- k-direction has turned over late four times, and every number here is
-- at a k this container can normalise.
------------------------------------------------------------------
module Frame-Mint-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _∸_; _⊔_; _*_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length; any)
open import Data.Fin  using (Fin; toℕ) renaming (zero to fz)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec  using (lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; Tick; Gas; hot; after_,_)
open import Rx.Exp  using (Ctx; Closed; Val; Tm; Fn; natᵗ; obs; _×ᵗ_; input;
                           ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Evaluator using (Slots; Sched; EvalSt; sched-next; budgetAt;
                                scripted;
                                Path; root; share-sink; _↠_;
                                RegId; Arrival; arrTy; arrVal; arrTick;
                                stepFrame; shareAdmit; shareLatch; shareFinish;
                                chainsOf; cascadeLatch)

open import Mint-Loop-Shapes using (runSt; mS; pA; insA; pB; insB)

------------------------------------------------------------------
-- THE MIRROR, carrying a PAIR of maxima instead of a fold count:
--
--   proj₁   the most registrations any single `stepFrame` added
--   proj₂   the widest payload list any single frame was handed
------------------------------------------------------------------

MM : Set
MM = ℕ × ℕ

_⊔₂_ : MM → MM → MM
(a , b) ⊔₂ (c , d) = (a ⊔ c) , (b ⊔ d)

fpM : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    → Gas → ℕ → Id → Tick
    → Path Γ u t → List (Val Γ u) → Bool
    → Sched Γ → EvalSt e → MM × Sched Γ × EvalSt e

dsM : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Gas → ℕ → Id → Tick → (i : Fin n)
    → List (Val Γ (lookup Γ i)) → Bool
    → Sched Γ → EvalSt e → MM × Sched Γ × EvalSt e

sgM : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Gas → ℕ → Id → Tick → (i : Fin n)
    → List (Val Γ (lookup Γ i)) → Bool
    → List (RegId × Path Γ (lookup Γ i) t)
    → Sched Γ → EvalSt e → MM × Sched Γ × EvalSt e

fpM sf gas id now root vals fin sched st = (0 , length vals) , sched , st
fpM sf gas id now (share-sink i) vals fin sched st =
  let (mm , sched′ , st′) = dsM sf gas id now i vals fin sched st
  in ((0 , length vals) ⊔₂ mm) , sched′ , st′
fpM sf gas id now (f ↠ p) vals fin sched st =
  let r₀ = EvalSt.nextReg st
      (vals′ , _ , fin′ , sched₁ , st₁) = stepFrame sf id now f p vals fin sched st
      (mm , sched₂ , st₂) = fpM sf gas id now p vals′ fin′ sched₁ st₁
  in ((EvalSt.nextReg st₁ ∸ r₀ , length vals) ⊔₂ mm) , sched₂ , st₂

dsM sf zero    id now i vals fin sched st = (0 , length vals) , sched , st
dsM sf (suc gas) id now i vals fin sched st =
  let (mm , sched₁ , st₁) =
        sgM sf gas id now i vals fin
          (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)
      (_ , sched₂ , st₂) = shareFinish i fin ([] , sched₁ , st₁)
  in mm , sched₂ , st₂

sgM sf gas id now i vals fin []               sched st = (0 , 0) , sched , st
sgM sf gas id now i vals fin ((rid , p) ∷ ps) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = sgM sf gas id now i vals fin ps sched st
... | false =
  let (mm₁ , sched₁ , st₁) =
        fpM sf gas id now p vals fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
      (mm₂ , sched₂ , st₂) = sgM sf gas id now i vals fin ps sched₁ st₁
  in (mm₁ ⊔₂ mm₂) , sched₂ , st₂

csM : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → (a : Arrival Γ) → Id → List (RegId × Path Γ (arrTy a) t)
    → Sched Γ → EvalSt e → MM × Sched Γ × EvalSt e
csM a id []                   sched st = (0 , 0) , sched , st
csM {n = n} {e = e} a id ((rid , c) ∷ chains) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = csM a id chains sched st
... | false =
  let (mm₁ , sched₁ , st₁) =
        fpM (budgetAt e (Sched.slots sched) id) n id (arrTick a) c
            (arrVal a ∷ []) (Arrival.isLast a) sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
      (mm₂ , sched₂ , st₂) = csM a id chains sched₁ st₁
  in (mm₁ ⊔₂ mm₂) , sched₂ , st₂

-- the two maxima over ONE cascade, the `fuel`-th one
fmAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → MM
fmAt fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = 0 , 0
...   | inj₂ (a , sched′) =
        proj₁ (csM a nid (chainsOf a st) sched′ (cascadeLatch a st))

-- the most registrations ONE frame minted
fmMint : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
fmMint fuel e ins = proj₁ (fmAt fuel e ins)

-- the widest payload list ONE frame was handed
fmWid : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
fmWid fuel e ins = proj₂ (fmAt fuel e ins)

------------------------------------------------------------------
-- THE WIDTH FAMILY.  The amplifier shapes are ONE payload wide, so
-- they say nothing about `Vb`'s width conjunct.  These are
-- Frame-Work-Probe's DEEPENING SCAN — an obs-typed accumulator that
-- re-wraps itself on every fold and is then unwrapped by a *All, the
-- sharpest known per-frame payload amplifier — put under one scripted
-- slot so that the run actually cascades and there are frames to
-- measure.
------------------------------------------------------------------

Γᵂ : Ctx 1
Γᵂ = natᵗ ∷ᵛ []ᵛ

-- one scripted slot, two emissions at tick 0 — the same script the
-- mint-loop ladders use, so the cascade structure is comparable
insᵂ : Slots Γᵂ
insᵂ fz = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

accV : ∀ {n} {Γ : Ctx n} → Tm Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ []) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

wrap1 wrap2 wrap3 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap1 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ [])))
wrap2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))
wrap3 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ accV ∷ [])))

seedW : ∀ {n} {Γ : Ctx n} → Tm Γ [] [] [] (obs natᵗ)
seedW = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

-- one syntactic level, the accumulator carrying 1 / 2^k / 3^k
w1 w2 w3 : Closed Γᵂ natᵗ
w1 = mergeAllᵉ (scanᵉ wrap1 seedW (input fz))
w2 = mergeAllᵉ (scanᵉ wrap2 seedW (input fz))
w3 = mergeAllᵉ (scanᵉ wrap3 seedW (input fz))

-- TWO syntactic levels: the inner run's payloads ARE the outer scan's
-- folds.  This is the shape whose per-frame payload count
-- Frame-Work-Probe read at 126
w4 : Closed Γᵂ natᵗ
w4 = mergeAllᵉ (scanᵉ wrap2 seedW (mergeAllᵉ (scanᵉ wrap2 seedW (input fz))))

------------------------------------------------------------------
-- THE ROWS, and the table they make.
--
-- `mS` is the tightest cSize the ENTRY state admits, so it is a FLOOR
-- on the cSize any admissible caps assignment carries — which makes
-- `fmMint ≤ mS` sufficient for `fmMint ≤ cSize * suc cWid` and a
-- comparison that needs no caps arithmetic.  It reproduces
-- Mint-Loop-Frames' published cSize column for pB (3 / 10 / 18 at
-- k = 0 / 1 / 2) exactly, which is this probe's calibration.
--
--   THE AMPLIFIER FAMILY — a minting scan inside a shared def, the
--   shapes where mints beget fires (Mint-Loop-Shapes MEASUREMENT 9):
--
--     program   k   cascade   fmMint   fmWid   mS
--     pA        0      0         1        1     3
--     pA        1      0         1        1    10
--     pB        0      0         1        1     3
--     pB        1      0         1        1    10
--     pB        2      0         1        1    18
--     pB        0      1         1        1     —
--     pB        1      1         1        1     —
--     pB        2      1         1        1     —
--
--   Every frame in the family mints exactly one registration and is
--   handed exactly one payload.  The mint budget is not close to being
--   tight here — 1 against a cSize floor of 3 to 18 — and the family is
--   ONE payload wide, so it says nothing about the width conjunct.
--
--   THE WIDTH FAMILY — the deepening scan, one scripted slot:
--
--     program   cascade   fmMint   fmWid
--     w1           0         0        1
--     w2           0         0        2
--     w3           0         0        3
--     w4           0         0        6
--     w2           1         0        4
--     w4           1         0      120
--
--   TWO THINGS TO READ, AND THE SECOND IS THE OPEN ONE.
--
--   (a) fmMint is 0 all down the width family.  These programs mint
--       nothing per frame at all: the deepening scan re-wraps an
--       accumulator and unwraps it through a *All, and the *All's
--       subscribes go to inner observables rather than to shared slots,
--       so no registration is created.  Every mint in the corpus is on
--       the amplifier family, and there it is 1.
--
--   (b) fmWid CLIMBS ACROSS ARRIVALS, hard: w4 is 6 wide at cascade 0
--       and 120 wide at cascade 1.  This is Frame-Work-Probe's ladder
--       (it recorded 2 ↦ 8 on a smaller shape) measured per FRAME
--       inside the cascade.  It is NOT by itself a breach of `Vb`,
--       because each cascade reads ITS OWN entry caps — `capsAt (suc
--       id)` is grown for cascade 1 — and within one cascade the number
--       does not move.  What it does say is that the width conjunct
--       `length vals ≤ suc cWid` is LOAD-BEARING and TIGHT-ish: it can
--       only hold if cWid at entry already carries the product that
--       outW takes at each *All (`outWᵉ (mergeAllᵉ e) = outWᵉ e *
--       innWᵉ e`), which is what outW was written to do.  Whether
--       `capsAt`'s cWid actually dominates 120 at cascade 1 is NOT
--       MEASURED here: `capsAt` is a tower and does not normalise in
--       the typechecker at these indices.  Recorded as the open
--       measurement, and it is the one that decides `stepFrame-entry-
--       caps`'s second conjunct
------------------------------------------------------------------

_ : fmMint 0 pA (insA 0) ≡ 1
_ = refl
_ : fmWid  0 pA (insA 0) ≡ 1
_ = refl
_ : mS     0 pA (insA 0) ≡ 3
_ = refl

_ : fmMint 0 pA (insA 1) ≡ 1
_ = refl
_ : fmWid  0 pA (insA 1) ≡ 1
_ = refl
_ : mS     0 pA (insA 1) ≡ 10
_ = refl

_ : fmMint 0 pB (insB 0) ≡ 1
_ = refl
_ : fmWid  0 pB (insB 0) ≡ 1
_ = refl
_ : mS     0 pB (insB 0) ≡ 3
_ = refl

_ : fmMint 0 pB (insB 1) ≡ 1
_ = refl
_ : fmWid  0 pB (insB 1) ≡ 1
_ = refl
_ : mS     0 pB (insB 1) ≡ 10
_ = refl

_ : fmMint 0 pB (insB 2) ≡ 1
_ = refl
_ : fmWid  0 pB (insB 2) ≡ 1
_ = refl
_ : mS     0 pB (insB 2) ≡ 18
_ = refl

_ : fmMint 1 pB (insB 0) ≡ 1
_ = refl
_ : fmWid  1 pB (insB 0) ≡ 1
_ = refl

_ : fmMint 1 pB (insB 1) ≡ 1
_ = refl
_ : fmWid  1 pB (insB 1) ≡ 1
_ = refl

_ : fmMint 1 pB (insB 2) ≡ 1
_ = refl
_ : fmWid  1 pB (insB 2) ≡ 1
_ = refl

_ : fmMint 0 w1 insᵂ ≡ 0
_ = refl
_ : fmWid  0 w1 insᵂ ≡ 1
_ = refl

_ : fmMint 0 w2 insᵂ ≡ 0
_ = refl
_ : fmWid  0 w2 insᵂ ≡ 2
_ = refl

_ : fmMint 0 w3 insᵂ ≡ 0
_ = refl
_ : fmWid  0 w3 insᵂ ≡ 3
_ = refl

_ : fmMint 0 w4 insᵂ ≡ 0
_ = refl
_ : fmWid  0 w4 insᵂ ≡ 6
_ = refl

_ : fmMint 1 w2 insᵂ ≡ 0
_ = refl
_ : fmWid  1 w2 insᵂ ≡ 4
_ = refl

_ : fmMint 1 w4 insᵂ ≡ 0
_ = refl
_ : fmWid  1 w4 insᵂ ≡ 120
_ = refl
