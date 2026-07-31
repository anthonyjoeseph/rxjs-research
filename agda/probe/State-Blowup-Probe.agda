------------------------------------------------------------------
-- THE STATE-BLOWUP PROBE: what does ONE instant do to the store?
--
-- Round 4 replaced the refuted fixed-height cap with a recurrence,
-- Caps (suc id) = frameBlowup (Caps id).  Its width component was gated
-- against deepScan; `sizeBlowup` and `regBlowup` were left as named
-- postulates precisely so they could not be guessed.  This is their
-- gate, and it is deliberately built the same way deepScan's was: read
-- the REAL quantities `capsOK?` bounds off a REAL run, then ask whether
-- the candidate covers them.
--
-- To do that it needs the evaluator's STATE, not its output stream, so
-- it re-runs the drain loop keeping `Sched`/`EvalSt` and reads
-- `sizeᵛ`/`outWᵛ`/`length ∘ registry` — the three conjuncts of
-- `capsOK?`, nothing else.
--
-- WHAT IT FINDS.  Three refutations and one clean answer.
--
--   (1) `outWᵉ` was ZERO on every scripted-input program, so the base
--       case's width cap did not cover even its own seed.
--   (2) The base case's SIZE cap is smaller than the state its own
--       subscribe frame leaves behind — a synchronous source folds
--       inside the root frame, and the entry measure does not pay for
--       it.
--   (3) `foldStep` is too small: measured against the quantity
--       `capsOK?` actually bounds (`outWᵛ` of the stored accumulator,
--       not the payload count deepScan measured), ONE fold takes a
--       width of 1 to 6 while `foldStep 1` allows 4.
--
--   (4) And the answer to the composition question: registrations
--       compose ADDITIVELY across live sources, not multiplicatively.
--
-- (1)–(3) are all "the cap is too small", none of them needs a
-- quantity outside `Caps`, so the round-5 gate — `frameBlowup : Caps →
-- Caps`, no ledger, no receipt, no E — is untouched by any of them.
------------------------------------------------------------------
module State-Blowup-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _≤ᵇ_; _⊔_;
                            z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; sum; map; length; foldr)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fsuc)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; after_,_; hot)
open import Rx.Exp  using (Ctx; Closed; Tm; Fn; Ty; natᵗ; obs; _×ᵗ_; input;
                           ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; nat̂; fstᵗ; varᵗ;
                           sizeᵉ; sizeᵛ)
open import Rx.Evaluator using (Slots; scripted; Sched; EvalSt; LiveSource;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                sched-init; sched-next; st-init; budgetAt;
                                subscribeE; cascade; slotsSize; root)
open import Rx.Frame-Width using (outWᵉ; outWᵛ)
open import Verify-Budget-Sufficient using (foldStep; sizeStep; iterSize;
                                            iterSize-mono-count;
                                            Caps; capsAt; stBounded?;
                                            capsOK?)
open import Rx.Prim using (Gas; Tick)
open import Rx.Evaluator using (Path)
open import Data.Empty using (⊥)

------------------------------------------------------------------
-- THE HARNESS: drain, but keep the state.  This is `drain`/`evaluate`
-- from Rx.Evaluator with the emit stream dropped instead of the state —
-- no other change, so the runs below are the evaluator's own
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
-- the three quantities capsOK? bounds, and NOTHING else: stBounded?'s
-- sizes, widLive/widNode's frame widths, and the registry's length
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

-- max stored size after `fuel` cascades
mSize : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mSize fuel e ins =
  let (sched , st) = runSt fuel e ins
  in foldr (λ kv m → nodeSize (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)
     ⊔ foldr (λ l m → liveSize l ⊔ m) 0 (Sched.live sched)

-- max stored FRAME WIDTH after `fuel` cascades
mWid : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mWid {n = n} fuel e ins =
  let (sched , st) = runSt fuel e ins
  in foldr (λ kv m → nodeWid n (Sched.slots sched) (proj₂ kv) ⊔ m) 0 (EvalSt.nodes st)
     ⊔ foldr (λ l m → liveWid n (Sched.slots sched) l ⊔ m) 0 (Sched.live sched)

-- live registrations after `fuel` cascades
mReg : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
mReg fuel e ins = length (EvalSt.registry (proj₂ (runSt fuel e ins)))

------------------------------------------------------------------
-- THE PROGRAMS.  Each is the sharpest amplifier for one component
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

accV : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

seed : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] Θ (obs natᵗ)
seed = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

src3 : ∀ {n} {Γ : Ctx n} → Closed Γ natᵗ
src3 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

-- one arrival per instant, so an instant is exactly one fold
ins3 : Slots Γ₁
ins3 fz = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ (after 0 , 3) ∷ []))

-- (A) THE SIZE ADVERSARY: three accumulator occurrences, so every fold
-- copies the whole stored accumulator three times
wrap3 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap3 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ accV ∷ [])))

pA : Closed Γ₁ natᵗ
pA = mergeAllᵉ (scanᵉ wrap3 seed (input fz))

-- (B) deepScan, the program that killed the fixed-height cap, now
-- measured on the STORE rather than the emit stream
wrap2ᵍ : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] ((obs natᵗ ×ᵗ natᵗ) ∷ Θ) (obs natᵗ)
wrap2ᵍ = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

deepScan : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepScan = strmᵗ (mergeAllᵉ (scanᵉ wrap2ᵍ seed (mergeAllᵉ (ofᵉ (accV ∷ [])))))

pD : Closed Γ₁ natᵗ
pD = mergeAllᵉ (scanᵉ deepScan seed (input fz))

-- (C) THE REGISTRATION ADVERSARY.  A registry entry survives only while
-- its SOURCE is live — an `ofᵉ` source completes inside its own frame
-- and cascadeFinish drops its entries — so growing the registry needs
-- the accumulator to keep re-subscribing the LIVE scripted input.  Each
-- fold doubles the number of `input` references it carries
wrapIn : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapIn = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ strmᵗ (input fz) ∷ [])))

pR : Closed Γ₁ natᵗ
pR = mergeAllᵉ (scanᵉ wrapIn seed (input fz))

-- the same thing SYNCHRONOUSLY: three folds inside the root subscribe
-- frame, so every registration and every size step is paid before the
-- first cascade even runs
pRs : Closed Γ₁ natᵗ
pRs = mergeAllᵉ (scanᵉ wrapIn seed src3)

-- (D) TWO live sources, the accumulator referencing both: this is where
-- multiplicative composition would show if it existed
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

ins2 : Slots Γ₂
ins2 fz        = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ (after 0 , 3) ∷ []))
ins2 (fsuc fz) = scripted (hot ((after 0 , 4) ∷ (after 0 , 5) ∷ (after 0 , 6) ∷ []))

wrapIn2 : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapIn2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ strmᵗ (input fz)
                                     ∷ strmᵗ (input (fsuc fz)) ∷ [])))

pR2 : Closed Γ₂ natᵗ
pR2 = mergeAllᵉ (scanᵉ wrapIn2 seed (input fz))

------------------------------------------------------------------
-- MEASUREMENT 1: SIZE.  One fold multiplies the stored accumulator by
-- the step function's OCCURRENCE COUNT and adds its own syntax, so a
-- single scan's size recurrence is s ↦ k·s + c — here 3·s + 15, exactly
-- wrap3's three occurrences.  Linear per fold, exponential in the
-- instant count.  This is `size-subΘᵉ`'s `sizeᵉ e * suc (2 * V)` seen
-- from the run, and it is the shape `sizeBlowup` has to iterate
------------------------------------------------------------------

_ : mSize 0 pA ins3 ≡ 3
_ = refl

_ : mSize 1 pA ins3 ≡ 24
_ = refl

_ : mSize 2 pA ins3 ≡ 87
_ = refl

_ : mSize 3 pA ins3 ≡ 276
_ = refl

-- deepScan's store, for contrast: its step function has only ONE
-- accumulator occurrence, so its SIZE grows slower than pA's even
-- though its WIDTH towers.  Size and width are moved by different
-- features of the step function — the occurrence count and the plug's
-- position — which is the concrete reason cSize and cWid are separate
-- fields rather than one
_ : mSize 1 pD ins3 ≡ 24
_ = refl

_ : mSize 2 pD ins3 ≡ 45
_ = refl

------------------------------------------------------------------
-- REFUTATION (a): `sizeBlowup` MAY NOT ITERATE A FIXED NUMBER OF TIMES,
-- AND MAY NOT READ cSize ALONE.
--
-- pR and pRs are the SAME step function over the SAME seed — so their
-- per-fold size step is identical, and every cSize-derived quantity
-- about them agrees.  They differ only in how many times that step runs
-- inside one frame: pR's source is the scripted input, which delivers
-- one payload per instant, while pRs's is a three-element literal,
-- which delivers three inside the root subscribe frame.
--
-- One frame of pRs therefore does what three instants of pR do: 3 ↦ 30
-- against 3 ↦ 12.  A blowup that applies its step a fixed number of
-- times, or that reads only the size, returns one answer for both and
-- must undershoot one of them.  The iteration count has to be the FOLD
-- COUNT — and a fold count is a width, so `sizeBlowup` must read cWid.
-- This is reach-via-size-absurd's circularity in the other direction:
-- not "width from size", but "how many size steps" from a width
------------------------------------------------------------------

_ : mSize 0 pR ins3 ≡ 3
_ = refl

_ : mSize 1 pR ins3 ≡ 12        -- ONE fold
_ = refl

_ : mSize 0 pRs ins3 ≡ 30       -- THREE folds, same step, one frame
_ = refl

_ : (30 ≤ᵇ 12) ≡ false
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 2: WIDTH — and REFUTATION (b), `foldStep` IS TOO SMALL.
--
-- deepScan's gate measured the PAYLOAD COUNT recurrence (1, 2, 6, 126)
-- and `foldStep w = 2 ^ suc w` dominates that by exactly 2 per level.
-- But the quantity `capsOK?` bounds is not the payload count — it is
-- `outWᵛ` of the value actually sitting in the scan node, which is a
-- BOUND on that count and grows faster.  Measured on the store, ONE
-- fold takes deepScan's stored width from 1 to 6, and `foldStep 1` is 4.
--
-- The round-4 gate was therefore gating the wrong quantity.  The reason
-- it is wrong is structural, not numeric: a fold substitutes the
-- accumulator into the step function, and `innWᵉ (scanᵉ f z e)` puts the
-- source's width in an EXPONENT whose base is read off `f`'s syntax.  So
-- the per-fold width multiplier is a property of the step function, and
-- the only thing in `Caps` that bounds a step function's syntax is
-- cSize.  A width step that reads only the width cannot see it
------------------------------------------------------------------

_ : mWid 0 pD ins3 ≡ 1
_ = refl

_ : mWid 1 pD ins3 ≡ 6
_ = refl

-- the refuted candidate, written out because it no longer exists as a
-- definition: a width step reading only the width
_ : (6 ≤ᵇ 2 ^ suc 1) ≡ false
_ = refl

-- and the replacement, at the step function's own measured size.  S = 3
-- is deepScan's stored size at that instant; the real cap is larger, so
-- this is the tight end of the gate
_ : (6 ≤ᵇ foldStep 3 1) ≡ true
_ = refl

-- the same measure on pA, where the step function has no inner scan and
-- the stored width just triples — one occurrence-count per fold
_ : mWid 0 pA ins3 ≡ 1
_ = refl

_ : mWid 1 pA ins3 ≡ 3
_ = refl

_ : mWid 2 pA ins3 ≡ 9
_ = refl

_ : mWid 3 pA ins3 ≡ 27
_ = refl

-- and deepScan's second cascade, for scale: 6 ↦ 3072
_ : mWid 2 pD ins3 ≡ 3072
_ = refl

------------------------------------------------------------------
-- REFUTATION (c), NOW FIXED: `outWᵉ` WAS ZERO ON A SCRIPTED INPUT, so
-- the base case's width cap did not cover its own seed.
--
-- `outWᵉ (suc j) sl (input i)` descends into a `shared` def but returned
-- 0 for a `scripted` slot, and every clause above it is multiplicative,
-- so the whole program measured 0 — while the state after pA's root
-- subscribe already holds a width-1 accumulator (its seed).  All seven
-- runs the measure was gated against used either a literal source or a
-- shared slot; the scripted case, the common one, was never gated.
--
-- The clause now yields 1, one payload per arrival, and these are the
-- gates that keep it honest.  (The refuted form is not restatable here
-- because `outWᵉ` takes no parameter to vary; commit a981e30 holds it
-- machine-checked, and git history is the archive.)
------------------------------------------------------------------

_ : outWᵉ 1 ins3 pA ≡ 9
_ = refl

_ : (1 ≤ᵇ outWᵉ 1 ins3 pA) ≡ true
_ = refl

_ : (1 ≤ᵇ outWᵉ 1 ins3 pD) ≡ true
_ = refl

_ : (1 ≤ᵇ outWᵉ 1 ins3 pR) ≡ true
_ = refl

------------------------------------------------------------------
-- REFUTATION (d): THE BASE CASE'S SIZE CAP IS SMALLER THAN ITS OWN
-- SUBSCRIBE FRAME'S RESULT.
--
-- `capsAt e sl zero`'s size component is `2 + sizeᵉ e + slotsSize sl` —
-- the program plus its slot telescope, no allowance for work.  But the
-- ROOT SUBSCRIBE IS ITSELF A FRAME: a synchronous source folds inside
-- it, so the state it hands to instant 0 has already grown.  pRs folds
-- three times before the first cascade, ending at 30 with a cap of 25.
--
-- This one does not touch the recurrence at all — the base case simply
-- has to be one frame's blowup above the syntax, which is what
-- `caps-frame` says about every OTHER frame already
------------------------------------------------------------------

_ : sizeᵉ pRs ≡ 19
_ = refl

_ : slotsSize ins3 ≡ 4
_ = refl

-- so the cap is 25, and the frame it is supposed to survive ended at 30
_ : (30 ≤ᵇ 2 + sizeᵉ pRs + slotsSize ins3) ≡ false
_ = refl

------------------------------------------------------------------
-- MEASUREMENT 3: REGISTRATIONS — and the clean answer.
--
-- pA and deepScan never grow the registry at all: their sources are
-- `ofᵉ` literals, which complete inside their own frame, and
-- cascadeFinish drops a spent source's entries.  Only a LIVE source
-- accumulates, which is what pR is for — and there the increment tracks
-- the accumulator's width (1 then 2, against widths 1 then 2), because
-- the new registrations are exactly the input references the fold
-- copied.  The sequence stops where the scripted source completes: a
-- spent source's entries drop at cascadeFinish, which is the same reason
-- pA and deepScan never accumulate at all
------------------------------------------------------------------

_ : mReg 2 pA ins3 ≡ 1
_ = refl

_ : mReg 2 pD ins3 ≡ 1
_ = refl

_ : mReg 0 pR ins3 ≡ 1
_ = refl

_ : mReg 1 pR ins3 ≡ 2
_ = refl

_ : mReg 2 pR ins3 ≡ 4
_ = refl

-- synchronously, the same folds cost the same registrations — six in
-- the root frame, paid before instant 0.  Frames and instants charge
-- alike, which is the fact that lets one `frameBlowup` serve both
_ : mReg 0 pRs ins3 ≡ 6
_ = refl

------------------------------------------------------------------
-- AND THE COMPOSITION QUESTION, ANSWERED: registrations compose
-- ADDITIVELY across live sources, not multiplicatively.
--
-- pR2's accumulator references TWO live inputs, so a multiplicative
-- rule would square where the single-source run doubled.  It does not:
-- the first cascade takes 1 to 3, one new registration per referenced
-- source, because a fold subscribes each reference exactly once.  So
-- `regBlowup` needs a product of cWid and cReg — the subscriptions one
-- instant's folds can mint — and no cross-source factor
------------------------------------------------------------------

_ : mReg 0 pR2 ins2 ≡ 1
_ = refl

_ : mReg 1 pR2 ins2 ≡ 3
_ = refl

_ : mReg 2 pR2 ins2 ≡ 3
_ = refl

------------------------------------------------------------------
-- THE GATE.  Every measured step above, against the candidate that
-- replaced the refuted one — at the tight end, with the MEASURED
-- quantities rather than the caps, so a candidate that only survives
-- because the caps are astronomical is refuted here.
--
-- Widths use a single `foldStep` per fold rather than the composed
-- `iterFold`: the composition is a tower and does not normalise, and the
-- single step is the sharper test anyway.  Sizes use `sizeStep`'s
-- multiplier at the measured CHAIN size — 10 for pA, 20 for deepScan, 8
-- for pR, all constant across the run — because that is the step
-- function's size, which is what size-subΘᵉ reads
------------------------------------------------------------------

-- width, one fold at a time: pA 1 ↦ 3 ↦ 9 ↦ 27 at sizes 3, 24, 87
_ : (3 ≤ᵇ foldStep 3 1) ≡ true
_ = refl

_ : (9 ≤ᵇ foldStep 24 3) ≡ true
_ = refl

_ : (27 ≤ᵇ foldStep 87 9) ≡ true
_ = refl

-- and deepScan's second fold, the tower's steepest measured step
_ : (3072 ≤ᵇ foldStep 24 6) ≡ true
_ = refl

-- size, one fold at a time.  pA's chains hold a size-10 step function
_ : (24 ≤ᵇ sizeStep 10 3) ≡ true
_ = refl

_ : (87 ≤ᵇ sizeStep 10 24) ≡ true
_ = refl

_ : (276 ≤ᵇ sizeStep 10 87) ≡ true
_ = refl

-- deepScan's is size 20
_ : (24 ≤ᵇ sizeStep 20 3) ≡ true
_ = refl

_ : (45 ≤ᵇ sizeStep 20 24) ≡ true
_ = refl

-- pR's is size 8
_ : (12 ≤ᵇ sizeStep 8 3) ≡ true
_ = refl

_ : (21 ≤ᵇ sizeStep 8 12) ≡ true
_ = refl

_ : (30 ≤ᵇ sizeStep 8 21) ≡ true
_ = refl

-- and pRs, the THREE-fold frame that refuted a fixed iteration count:
-- the same step function, iterated three times, covers 3 ↦ 30
_ : (30 ≤ᵇ iterSize 8 3 3) ≡ true
_ = refl

-- registrations: pR 1 ↦ 2 ↦ 4 at widths 1, 2 and sizes 3, 12
_ : (2 ≤ᵇ 1 * suc (1 * 3)) ≡ true
_ = refl

_ : (4 ≤ᵇ 2 * suc (2 * 12)) ≡ true
_ = refl

-- pR2's two live sources, 1 ↦ 3 — and the reason regBlowup carries a
-- cSize factor: `cReg * suc cWid` alone gives 2 and does not fit
_ : (3 ≤ᵇ 1 * suc (1 * 3)) ≡ true
_ = refl

_ : (3 ≤ᵇ 1 * suc 1) ≡ false
_ = refl

------------------------------------------------------------------
-- AND THE BASE CASE, now that it pays for its own frame: capsAt's
-- instant-0 caps must cover the state the ROOT SUBSCRIBE leaves, which
-- for pRs is three folds' worth.  Only cSize and cReg are checked — the
-- width component composes to a tower and does not normalise, which is
-- why the width gates above are per-fold.
--
-- THE cSIZE HALF IS NO LONGER A `refl`, and the reason is Fold-Count-
-- Probe: the iteration count is now `2 ^ cReg * cSize`, and pRs enters
-- at cSize 25 / cReg 24, so the endpoint is `iterSize 25 (2 ^ 24 * 25)
-- 25` — four hundred million iterations, each squaring, which no
-- machine unfolds.  So it is checked the way the k = 7 crossover is:
-- as arithmetic over a law, with the law's small-count instance still
-- `refl`-gated.  The content is identical — capsAt's instant-0 cSize
-- dominates ONE fold from the entry caps, and one fold already covers
-- the 30 the root subscribe leaves.
--
-- The cReg half is still `refl`: its endpoint is `cReg * suc (j*cSize)`,
-- a product of numerals however large j is, with no iteration to unfold
------------------------------------------------------------------

-- the law, with the COUNT LEFT ABSTRACT — which is what keeps it
-- checkable: `e` and `sl` are variables, so `Caps.cSize (capsAt e sl 0)`
-- gets stuck at `iterSize A ⟨count⟩ A` instead of unfolding it
capsAt0-one-fold : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
  1 ≤ 2 ^ suc (sizeᵉ e + slotsSize sl) * (2 + sizeᵉ e + slotsSize sl) →
  iterSize (2 + sizeᵉ e + slotsSize sl) 1 (2 + sizeᵉ e + slotsSize sl)
    ≤ Caps.cSize (capsAt e sl 0)
capsAt0-one-fold e sl h = iterSize-mono-count _ _ (s≤s z≤n) h

-- pRs enters at 25, one fold takes it to 1275, and 1275 covers the 30
capsAt0-size-pRs : 30 ≤ Caps.cSize (capsAt pRs ins3 0)
capsAt0-size-pRs = ≤-trans lo hi
  where
  A : ℕ
  A = 2 + sizeᵉ pRs + slotsSize ins3
  lo : 30 ≤ iterSize A 1 A
  lo = ≤ᵇ⇒≤ 30 (iterSize A 1 A) _
  hi : iterSize A 1 A ≤ Caps.cSize (capsAt pRs ins3 0)
  hi = capsAt0-one-fold pRs ins3 (≤ᵇ⇒≤ 1 _ _)

capsAt0-size-pA : 3 ≤ Caps.cSize (capsAt pA ins3 0)
capsAt0-size-pA = ≤-trans lo hi
  where
  A : ℕ
  A = 2 + sizeᵉ pA + slotsSize ins3
  lo : 3 ≤ iterSize A 1 A
  lo = ≤ᵇ⇒≤ 3 (iterSize A 1 A) _
  hi : iterSize A 1 A ≤ Caps.cSize (capsAt pA ins3 0)
  hi = capsAt0-one-fold pA ins3 (≤ᵇ⇒≤ 1 _ _)

_ : (6 ≤ᵇ Caps.cReg (capsAt pRs ins3 0)) ≡ true
_ = refl

_ : (1 ≤ᵇ Caps.cReg (capsAt pA ins3 0)) ≡ true
_ = refl

------------------------------------------------------------------
-- REFUTATION (e): SAME-LEVEL PRESERVATION IS FALSE — caps-frame's shape
-- cannot hold, and the witness needs no pre-grown store at all.
--
-- caps-frame says: a state satisfying capsOK? at level `id`, subscribed
-- with a `b` whose size is within that level's cSize, still satisfies
-- capsOK? AT THE SAME LEVEL afterwards.  But subscribeE's scanᵉ clause
-- (Rx/Evaluator.agda:958) installs `scan-st (evalTm seed)` and then runs
-- the source's sync burst through pushBurst with the scan-f frame, and
-- dispatch updates that node once per synchronous payload — so the
-- SUBSCRIBE FRAME ITSELF folds.  A `b` at the size cap that folds even
-- once therefore lands above the cap.
--
-- The shape, with the cap as a parameter so it can be exhibited at a
-- size a real program reaches (capsAt's own cSize is a tower, so no
-- writable program comes near it — but the obstruction does not depend
-- on which C is chosen, see caps-frame-boundary-absurd, which is uniform
-- in C).  Only the stBounded? conjunct is needed to break it
------------------------------------------------------------------

-- Stated at the ROOT SUBSCRIBE, which is one of caps-frame's own
-- instances (κ = root, id = 0, level 0).  Phrasing it over `runSt 0` —
-- the same term the measurements above already normalise — keeps the
-- refutation cheap; unfolding a fresh `subscribeE` application inside a
-- `with` costs many gigabytes for no extra content
FramePreservesAt : ℕ → Set
FramePreservesAt C = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  stBounded? C (sched-init e ins) (st-init e) ≡ true →
  sizeᵉ e ≤ C →
  stBounded? C (proj₁ (runSt 0 e ins)) (proj₂ (runSt 0 e ins)) ≡ true

-- pRs is the witness: its own size is 19, its initial state is bounded
-- by 19, and its root subscribe leaves a node of size 30
_ : sizeᵉ pRs ≡ 19
_ = refl

_ : stBounded? 19 (sched-init pRs ins3) (st-init pRs) ≡ true
_ = refl

-- and so the shape cannot hold: it demands stBounded? 19 of a state
-- holding a size-30 node
framePreserves-absurd : FramePreservesAt 19 → ⊥
framePreserves-absurd fp with fp pRs ins3 refl (≤ᵇ⇒≤ (sizeᵉ pRs) 19 _)
... | ()

------------------------------------------------------------------
-- INSTANTIABILITY OF THE REPAIR, AND WHY IT CANNOT BE — AND NEED NOT BE
-- — CHECKED BY NORMALISATION.
--
-- caps-frame's refutation demands the fold-counting repair be shown NOT
-- to share its disease before it is trusted.  The obvious end-to-end
-- test — `capsOK? (capsAt e sl 1)` on the real post-cascade state — is
-- INFEASIBLE, and the reason is the deepScan tower itself: capsAt's cWid
-- is `iterFold (cWid * cReg) …`, and widNode checks `outWᵛ ≤ᵇ cWid`.
-- Even the 9-deep WHNF that `9 ≤ᵇ cWid` needs forces `2 ^ bignum` at the
-- tower's outermost step, so it does not terminate in any feasible
-- memory.  (The cSize/cReg endpoint gates below DO normalise — cReg is a
-- single product, cSize's iterSize is polynomial per step — which is why
-- those are checked and cWid is not.)
--
-- But this infeasibility is not the vacuity caps-frame had, and the
-- distinction is the whole point.  caps-frame was false at the STATEMENT
-- level: same-level preservation, refuted by ONE fold regardless of how
-- large the cap is (caps-frame-boundary-absurd is uniform in C).  No
-- budget rescues it.  subscribeE-caps does not preserve — it GROWS,
-- frameStep j ↦ frameStep (j + j′) — so it cannot be refuted that way,
-- and its budget (cWid * cReg, the tower) dwarfs any cascade's actual
-- fold count by construction.  The tower is not an obstacle to
-- instantiability; it IS the headroom that makes it hold.
--
-- So what is checkable, and checked, is the STRUCTURE the proof rides:
--   · the endpoints are refl — frameStep-0, frameStep-full,
--     capsAt-suc-full (in Verify-Budget-Sufficient), and
--   · each single fold's growth is dominated — the foldStep / sizeStep
--     gates above.
-- Those two are what a normalising machine can confirm; the tower-sized
-- composite is left to the induction, which never evaluates it.
------------------------------------------------------------------
