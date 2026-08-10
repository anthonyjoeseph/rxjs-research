-- ROADMAP: ROUTE GUARD — `old-cDel<=new-cDel` justifies the live cDel design (Rx/Evaluator.agda:505,572).
-- DELETE WHEN: The-Proof.agda is discharged — a dead route cannot be retried once the proof is done  [T7]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
------------------------------------------------------------------
-- THE EVOLVING-CAPS DELIVERY WALK, PROBED BEFORE IT IS LANDED — and
-- the GATE that says landing it costs no re-measurement.
--
-- WHY A NEW WALK.  `dCap` / `dWalk` (Rx.Evaluator) thread a REGISTRY:
-- the walk's (i+1)-st summand runs at `R + Q · suc d`, Q a per-delivery
-- mint budget read once at the cascade's ENTRY caps.  Charging anything
-- per-frame at the entry caps is REFUTED (Entry-Caps-Refuted: one map-f
-- frame's output breaches the entry cap it was charged at, because
-- `applyFn` grows a value), and the honest per-frame face — the PROVEN
-- `stepFrame-caps` — reports a growth index j′ and lands its post-state
-- at `frameStep (j + j′) c`.  So the walk has to carry the LEVEL, not a
-- fixed Q: each delivery's frames grow the level by their own receipts,
-- receipts read at the level the frame RUNS at, and the registry a
-- later dispatch sees is then read off THAT level — `capsOK?`'s own
-- fifth conjunct is `length registry ≤ cReg (frameStep J c)`, so the
-- registry bound is a FUNCTION OF THE LEVEL and needs no separate mint
-- accounting at all.
--
-- AND THE BUMP IS PER FRAME, NOT PER DELIVERY.  A delivery's chain is
-- frames, and each frame runs at the level the one before it LEFT, so a
-- delivery's charge is an ITERATION (`iterL`, `suc (sizeAt S J)` of
-- them — `pathSz?`'s length conjunct read at the delivery's entry
-- level) and not a product.  Charging a delivery's frames at the level
-- the DELIVERY started from would be the same error one level down that
-- charging a cascade's frames at its ENTRY caps is, and that error is
-- machine-refuted.  The old per-delivery product survives only as
-- `chargeAt`, which is what the gate below is stated against.
--
-- WHAT IS PROVEN HERE, on self-contained copies of the repo's
-- arithmetic (so the probe costs no rebuild of the tree):
--
--   § A  the recursion TERMINATES on the same lexicographic (gas, walk
--        position) descent the old one does, `lvls` composes
--        (`lvls-add`), and the walk DECOMPOSES FROM THE FRONT
--        (`dWalkᶜ-front`) — an equality, which is the one identity the
--        head-first evaluator walk consumes.
--   § B  the level reading is monotone in every argument.
--   § C  so is the walk: `dCapᶜ-mono` / `dWalkᶜ-mono` in S, W, R, gas
--        AND level, by the same lexicographic descent (this is what the
--        pooled count `poolCount` needs to keep dominating `sizeCount`).
--   § D  THE GATE.  `old≤new-cap` / `old-cDel≤new-cDel`: at the same
--        entry caps the level walk is POINTWISE ABOVE the registry walk
--        it replaces (2 ≤ cSize, 1 ≤ cReg).  `chargeAt S W 0` IS
--        `chargeW` of the entry caps and `regAt S R 0` IS the entry
--        registry, so no measured D row has to be re-run: every row the
--        old `cDel` cleared, the new one clears with the same margin or
--        more.  The mechanism is the obvious one made precise — the
--        level after d deliveries is at least `d · chargeW` up
--        (`lvls-lin`), and one level costs the registry a FACTOR
--        (`regAt S R J = R · suc (J · S)`) where the old walk paid a
--        summand.  `count-gate` is that same fact read at the CAPS
--        RECURRENCE's instant: `sizeCount` is now `lvls S W 0 D` where
--        it was `D · S · fCharge S W 0`, and the level dominates the
--        product, so no Instant-Height row is re-measured either.
------------------------------------------------------------------
module Level-Walk-Probe where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

------------------------------------------------------------------
-- copies of the repo's arithmetic (Verify-Budget-Sufficient.Caps)
------------------------------------------------------------------

foldStep : ℕ → ℕ → ℕ
foldStep S w = S ^ suc w

iterFold : ℕ → ℕ → ℕ → ℕ
iterFold S zero    w = w
iterFold S (suc k) w = iterFold S k (foldStep S w)

sizeStep : ℕ → ℕ → ℕ
sizeStep S s = S * suc (2 * s)

iterSize : ℕ → ℕ → ℕ → ℕ
iterSize S zero    s = s
iterSize S (suc k) s = iterSize S k (sizeStep S s)

-- the OLD walk, for the domination gate
dCap  : ℕ → ℕ → ℕ → ℕ
dWalk : ℕ → ℕ → ℕ → ℕ → ℕ
dCap Q zero    R = 0
dCap Q (suc g) R = dWalk Q g R R
dWalk Q g R zero    = 0
dWalk Q g R (suc i) =
  let d = dWalk Q g R i
  in d + suc (dCap Q g (R + Q * suc d))

------------------------------------------------------------------
-- THE LEVEL READING: the three caps fields at level J of `frameStep`,
-- in raw fields (frameStep j c = caps (iterSize S j S) (iterFold S j W)
-- (R * suc (j * S)))
------------------------------------------------------------------

sizeAt : ℕ → ℕ → ℕ
sizeAt S J = iterSize S J S

widAt : ℕ → ℕ → ℕ → ℕ
widAt S W J = iterFold S J W

regAt : ℕ → ℕ → ℕ → ℕ
regAt S R J = R * suc (J * S)

-- ONE FRAME'S RECEIPT, READ AT THE LEVEL THE FRAME RUNS AT.  The
-- receipt `scanFrame-caps` pays is `suc (length vals * suc (sizeᵗ fn))`
-- — one fold per node of the step function PER PAYLOAD — and at level J
-- its two factors are the width cap `suc (cWid (frameStep J c))` (the
-- burst ledger's own conjunct) and the size cap `cSize (frameStep J c)`
fCharge : ℕ → ℕ → ℕ → ℕ
fCharge S W J = suc (suc (widAt S W J) * suc (sizeAt S J))

-- and ONE FRAME advances the level by exactly that
fLvl : ℕ → ℕ → ℕ → ℕ
fLvl S W J = J + fCharge S W J

-- A CHAIN IS FRAMES, AND EACH FRAME RUNS AT THE LEVEL THE ONE BEFORE IT
-- LEFT — this is the whole point, and it is why a delivery's charge is
-- an ITERATION rather than a product.  Charging a delivery's frames at
-- the level the DELIVERY started from is the same error one level down
-- that charging a cascade's frames at the cascade's entry caps is, and
-- that error is machine-refuted (Entry-Caps-Refuted)
iterL : ℕ → ℕ → ℕ → ℕ → ℕ
iterL S W zero    J = J
iterL S W (suc k) J = iterL S W k (fLvl S W J)

-- ONE DELIVERY: its chain, which `pathSz?`'s length conjunct caps at
-- `cSize` READ AT ITS ENTRY LEVEL, plus the dispatch frame
dLvl : ℕ → ℕ → ℕ → ℕ
dLvl S W J = iterL S W (suc (sizeAt S J)) J

-- the level after d deliveries
lvls : ℕ → ℕ → ℕ → ℕ → ℕ
lvls S W J zero    = J
lvls S W J (suc d) = dLvl S W (lvls S W J d)

-- the OLD per-delivery charge, kept only to state the gate: it is
-- `chargeW` of the caps at level J, i.e. a whole chain charged at the
-- level the chain STARTED at
chargeAt : ℕ → ℕ → ℕ → ℕ
chargeAt S W J = sizeAt S J * fCharge S W J

------------------------------------------------------------------
-- THE WALK, CARRYING THE LEVEL INSTEAD OF THE REGISTRY
------------------------------------------------------------------

dCapᶜ  : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ       -- S W R gas J
dWalkᶜ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ   -- S W R gas J position

dCapᶜ S W R zero    J = 0
dCapᶜ S W R (suc g) J = dWalkᶜ S W R g J (regAt S R J)

dWalkᶜ S W R g J zero    = 0
dWalkᶜ S W R g J (suc i) =
  let d = dWalkᶜ S W R g J i
  in d + suc (dCapᶜ S W R g (lvls S W J (suc d)))

------------------------------------------------------------------
-- § A.  THE LEVEL COMPOSES, so the walk decomposes from the FRONT
------------------------------------------------------------------

lvls-add : ∀ (S W J a b : ℕ) →
  lvls S W J (a + b) ≡ lvls S W (lvls S W J a) b
lvls-add S W J a zero    = cong (lvls S W J) (+-identityʳ a)
lvls-add S W J a (suc b) =
  trans (cong (lvls S W J) (+-suc a b))
        (cong (dLvl S W) (lvls-add S W J a b))

dWalkᶜ-front : ∀ (S W R g J i : ℕ) →
  dWalkᶜ S W R g J (suc i)
    ≡ suc (dCapᶜ S W R g (lvls S W J 1))
      + dWalkᶜ S W R g (lvls S W J (suc (dCapᶜ S W R g (lvls S W J 1)))) i
dWalkᶜ-front S W R g J zero =
  sym (+-identityʳ (suc (dCapᶜ S W R g (lvls S W J 1))))
dWalkᶜ-front S W R g J (suc i) =
  trans (cong (λ x → x + suc (dCapᶜ S W R g (lvls S W J (suc x))))
              (dWalkᶜ-front S W R g J i))
    (trans (+-assoc (suc A) W′ (suc (dCapᶜ S W R g (lvls S W J (suc (suc A + W′))))))
           (cong (λ x → suc A + (W′ + suc (dCapᶜ S W R g x))) (sym re)))
  where
  A  = dCapᶜ S W R g (lvls S W J 1)
  J′ = lvls S W J (suc A)
  W′ = dWalkᶜ S W R g J′ i
  re : lvls S W J′ (suc W′) ≡ lvls S W J (suc (suc A + W′))
  re = trans (sym (lvls-add S W J (suc A) (suc W′)))
             (cong (lvls S W J) (trans (+-suc (suc A) W′) refl))

------------------------------------------------------------------
-- § B.  MONOTONICITY OF THE LEVEL READING
------------------------------------------------------------------

sizeStep-mono : ∀ {S S′ s s′} → S ≤ S′ → s ≤ s′ → sizeStep S s ≤ sizeStep S′ s′
sizeStep-mono hS hs = *-mono-≤ hS (s≤s (*-monoʳ-≤ 2 hs))

foldStep-mono : ∀ {S S′ w w′} → 2 ≤ S → S ≤ S′ → w ≤ w′ →
  foldStep S w ≤ foldStep S′ w′
foldStep-mono {zero}        {S′} {w} {w′} ()  hS hw
foldStep-mono {suc zero}    {S′} {w} {w′} (s≤s ()) hS hw
foldStep-mono {suc (suc n)} {S′} {w} {w′} 2≤S hS hw =
  ≤-trans (^-monoʳ-≤ (suc (suc n)) (s≤s hw)) (^-monoˡ-≤ (suc w′) hS)

iterSize-base : ∀ (k : ℕ) {S S′ s s′} → S ≤ S′ → s ≤ s′ →
  iterSize S k s ≤ iterSize S′ k s′
iterSize-base zero    hS hs = hs
iterSize-base (suc k) hS hs = iterSize-base k hS (sizeStep-mono hS hs)

iterFold-base : ∀ (k : ℕ) {S S′ w w′} → 2 ≤ S → S ≤ S′ → w ≤ w′ →
  iterFold S k w ≤ iterFold S′ k w′
iterFold-base zero    2≤S hS hw = hw
iterFold-base (suc k) 2≤S hS hw =
  iterFold-base k 2≤S hS (foldStep-mono 2≤S hS hw)

s≤2s : ∀ (s : ℕ) → s ≤ 2 * s
s≤2s s = m≤m+n s (s + 0)

sizeStep-infl : ∀ (S s : ℕ) → 1 ≤ S → s ≤ sizeStep S s
sizeStep-infl S s hS =
  ≤-trans (≤-trans (s≤2s s) (n≤1+n (2 * s)))
          (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * s)))))
                   (*-monoˡ-≤ (suc (2 * s)) hS))

iterSize-infl : ∀ (S : ℕ) → 1 ≤ S → ∀ (k s : ℕ) → s ≤ iterSize S k s
iterSize-infl S hS zero    s = ≤-refl
iterSize-infl S hS (suc k) s =
  ≤-trans (sizeStep-infl S s hS) (iterSize-infl S hS k (sizeStep S s))

iterSize-count : ∀ (S s : ℕ) → 1 ≤ S → ∀ {k k′} → k ≤ k′ →
  iterSize S k s ≤ iterSize S k′ s
iterSize-count S s hS {k′ = k′} z≤n     = iterSize-infl S hS k′ s
iterSize-count S s hS          (s≤s le) = iterSize-count S (sizeStep S s) hS le

1≤2^ : ∀ (k : ℕ) → 1 ≤ 2 ^ k
1≤2^ zero    = ≤-refl
1≤2^ (suc k) = ≤-trans (1≤2^ k) (m≤m+n (2 ^ k) (2 ^ k + 0))

sucn≤2^n : ∀ (n : ℕ) → suc n ≤ 2 ^ n
sucn≤2^n zero    = ≤-refl
sucn≤2^n (suc k) =
  ≤-trans (s≤s (sucn≤2^n k)) (+-mono-≤ (1≤2^ k) (m≤m+n (2 ^ k) 0))

foldStep-infl : ∀ (S w : ℕ) → 2 ≤ S → w ≤ foldStep S w
foldStep-infl S w hS =
  ≤-trans (≤-trans (n≤1+n w) (sucn≤2^n w))
          (≤-trans (^-monoʳ-≤ 2 (n≤1+n w)) (^-monoˡ-≤ (suc w) hS))

iterFold-infl : ∀ (S : ℕ) → 2 ≤ S → ∀ (k w : ℕ) → w ≤ iterFold S k w
iterFold-infl S hS zero    w = ≤-refl
iterFold-infl S hS (suc k) w =
  ≤-trans (foldStep-infl S w hS) (iterFold-infl S hS k (foldStep S w))

iterFold-count : ∀ (S w : ℕ) → 2 ≤ S → ∀ {k k′} → k ≤ k′ →
  iterFold S k w ≤ iterFold S k′ w
iterFold-count S w hS {k′ = k′} z≤n     = iterFold-infl S hS k′ w
iterFold-count S w hS          (s≤s le) = iterFold-count S (foldStep S w) hS le

------------------------------------------------------------------
-- § C.  THE WALK IS MONOTONE IN EVERY ARGUMENT, level included
------------------------------------------------------------------

sizeAt-mono : ∀ {S S′ J J′} → 1 ≤ S → S ≤ S′ → J ≤ J′ → sizeAt S J ≤ sizeAt S′ J′
sizeAt-mono {S} {S′} {J} {J′} 1≤S hS hJ =
  ≤-trans (iterSize-base J hS hS) (iterSize-count S′ S′ (≤-trans 1≤S hS) hJ)

widAt-mono : ∀ {S S′ W W′ J J′} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  widAt S W J ≤ widAt S′ W′ J′
widAt-mono {S} {S′} {W} {W′} {J} {J′} 2≤S hS hW hJ =
  ≤-trans (iterFold-base J 2≤S hS hW) (iterFold-count S′ W′ (≤-trans 2≤S hS) hJ)

regAt-mono : ∀ {S S′ R R′ J J′} → S ≤ S′ → R ≤ R′ → J ≤ J′ →
  regAt S R J ≤ regAt S′ R′ J′
regAt-mono hS hR hJ = *-mono-≤ hR (s≤s (*-mono-≤ hJ hS))

fCharge-mono : ∀ {S S′ W W′ J J′} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  fCharge S W J ≤ fCharge S′ W′ J′
fCharge-mono 2≤S hS hW hJ =
  s≤s (*-mono-≤ (s≤s (widAt-mono 2≤S hS hW hJ))
                (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ)))

chargeAt-mono : ∀ {S S′ W W′ J J′} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  chargeAt S W J ≤ chargeAt S′ W′ J′
chargeAt-mono 2≤S hS hW hJ =
  *-mono-≤ (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ) (fCharge-mono 2≤S hS hW hJ)

fLvl-mono : ∀ {S S′ W W′ J J′} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  fLvl S W J ≤ fLvl S′ W′ J′
fLvl-mono 2≤S hS hW hJ = +-mono-≤ hJ (fCharge-mono 2≤S hS hW hJ)

iterL-infl : ∀ (S W k J : ℕ) → J ≤ iterL S W k J
iterL-infl S W zero    J = ≤-refl
iterL-infl S W (suc k) J = ≤-trans (m≤m+n J _) (iterL-infl S W k (fLvl S W J))

iterL-mono : ∀ {S S′ W W′ J J′} (k k′ : ℕ) → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  k ≤ k′ → iterL S W k J ≤ iterL S′ W′ k′ J′
iterL-mono {S′ = S′} {W′ = W′} {J′ = J′} zero k′ 2≤S hS hW hJ hk =
  ≤-trans hJ (iterL-infl S′ W′ k′ J′)
iterL-mono (suc k) zero    2≤S hS hW hJ ()
iterL-mono (suc k) (suc k′) 2≤S hS hW hJ (s≤s hk) =
  iterL-mono k k′ 2≤S hS hW (fLvl-mono 2≤S hS hW hJ) hk

dLvl-infl : ∀ (S W J : ℕ) → J ≤ dLvl S W J
dLvl-infl S W J = iterL-infl S W (suc (sizeAt S J)) J

dLvl-mono : ∀ {S S′ W W′ J J′} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  dLvl S W J ≤ dLvl S′ W′ J′
dLvl-mono {S} {S′} {W} {W′} {J} {J′} 2≤S hS hW hJ =
  iterL-mono (suc (sizeAt S J)) (suc (sizeAt S′ J′)) 2≤S hS hW hJ
             (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ))

lvls-infl : ∀ (S W J d : ℕ) → J ≤ lvls S W J d
lvls-infl S W J zero    = ≤-refl
lvls-infl S W J (suc d) = ≤-trans (lvls-infl S W J d) (dLvl-infl S W (lvls S W J d))

lvls-mono : ∀ {S S′ W W′ J J′} (d d′ : ℕ) → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  d ≤ d′ → lvls S W J d ≤ lvls S′ W′ J′ d′
lvls-mono {S′ = S′} {W′ = W′} {J′ = J′} zero d′ 2≤S hS hW hJ hd =
  ≤-trans hJ (lvls-infl S′ W′ J′ d′)
lvls-mono (suc d) zero    2≤S hS hW hJ ()
lvls-mono (suc d) (suc d′) 2≤S hS hW hJ (s≤s hd) =
  dLvl-mono 2≤S hS hW (lvls-mono d d′ 2≤S hS hW hJ hd)

dCapᶜ-mono : ∀ {S S′ W W′ R R′ J J′} (g g′ : ℕ) →
  2 ≤ S → S ≤ S′ → W ≤ W′ → R ≤ R′ → g ≤ g′ → J ≤ J′ →
  dCapᶜ S W R g J ≤ dCapᶜ S′ W′ R′ g′ J′
dWalkᶜ-mono : ∀ {S S′ W W′ R R′ J J′} (g g′ i i′ : ℕ) →
  2 ≤ S → S ≤ S′ → W ≤ W′ → R ≤ R′ → g ≤ g′ → J ≤ J′ → i ≤ i′ →
  dWalkᶜ S W R g J i ≤ dWalkᶜ S′ W′ R′ g′ J′ i′

dCapᶜ-mono zero    g′       2≤S hS hW hR hg       hJ = z≤n
dCapᶜ-mono (suc g) zero     2≤S hS hW hR ()       hJ
dCapᶜ-mono (suc g) (suc g′) 2≤S hS hW hR (s≤s hg) hJ =
  dWalkᶜ-mono g g′ _ _ 2≤S hS hW hR hg hJ (regAt-mono hS hR hJ)

dWalkᶜ-mono g g′ zero    i′       2≤S hS hW hR hg hJ hi       = z≤n
dWalkᶜ-mono g g′ (suc i) zero     2≤S hS hW hR hg hJ ()
dWalkᶜ-mono g g′ (suc i) (suc i′) 2≤S hS hW hR hg hJ (s≤s hi) =
  +-mono-≤ ih (s≤s (dCapᶜ-mono g g′ 2≤S hS hW hR hg
                      (lvls-mono (suc _) (suc _) 2≤S hS hW hJ (s≤s ih))))
  where
  ih = dWalkᶜ-mono g g′ i i′ 2≤S hS hW hR hg hJ hi

------------------------------------------------------------------
-- § D.  THE GATE: THE LEVEL WALK DOMINATES THE OLD REGISTRY WALK, at
-- the same entry caps.  So every row the old `cDel` was gated against
-- is a row the new one clears, with no new measurement.
------------------------------------------------------------------

-- the level after d deliveries is at least d entry-charges up
-- k frames each add at least one frame-charge read at the entry level
iterL-lin : ∀ (S W k J : ℕ) → 2 ≤ S → J + k * fCharge S W J ≤ iterL S W k J
iterL-lin S W zero    J 2≤S = ≤-reflexive (+-identityʳ J)
iterL-lin S W (suc k) J 2≤S =
  ≤-trans (≤-reflexive (re J (fCharge S W J) k))
          (≤-trans (+-monoʳ-≤ (fLvl S W J)
                      (*-monoʳ-≤ k (fCharge-mono 2≤S ≤-refl ≤-refl
                                      (m≤m+n J (fCharge S W J)))))
                   (iterL-lin S W k (fLvl S W J) 2≤S))
  where
  re : ∀ (j q k : ℕ) → j + (q + k * q) ≡ (j + q) + k * q
  re = solve 3 (λ j q k → j :+ (q :+ k :* q) := (j :+ q) :+ k :* q) refl

-- so ONE delivery is at least ONE old per-delivery charge up: its chain
-- has `suc (sizeAt S J) ≥ sizeAt S 0` frames and each is charged at a
-- level at or above the entry one
dLvl-lin : ∀ (S W J : ℕ) → 2 ≤ S → J + chargeAt S W 0 ≤ dLvl S W J
dLvl-lin S W J 2≤S =
  ≤-trans (+-monoʳ-≤ J (*-mono-≤ sz≤ (fCharge-mono 2≤S ≤-refl ≤-refl (z≤n {J}))))
          (iterL-lin S W (suc (sizeAt S J)) J 2≤S)
  where
  sz≤ : sizeAt S 0 ≤ suc (sizeAt S J)
  sz≤ = ≤-trans (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl (z≤n {J}))
                (n≤1+n (sizeAt S J))

lvls-lin : ∀ (S W J d : ℕ) → 2 ≤ S → J + d * chargeAt S W 0 ≤ lvls S W J d
lvls-lin S W J zero    2≤S = ≤-reflexive (+-identityʳ J)
lvls-lin S W J (suc d) 2≤S =
  ≤-trans (≤-reflexive (re J (chargeAt S W 0) d))
          (≤-trans (+-monoˡ-≤ (chargeAt S W 0) (lvls-lin S W J d 2≤S))
                   (dLvl-lin S W (lvls S W J d) 2≤S))
  where
  re : ∀ (j q d : ℕ) → j + (q + d * q) ≡ (j + d * q) + q
  re = solve 3 (λ j q d → j :+ (q :+ d :* q) := (j :+ d :* q) :+ q) refl

-- THE COUNT GATE, and it is the same fact read at the caps recurrence's
-- own instant.  `sizeCount` (Verify-Budget-Sufficient.Caps) is now
-- `lvls S W 0 D` where it was `D * S * fCharge S W 0` — a whole cascade
-- charged at its ENTRY level.  `chargeAt S W 0` IS `S * fCharge S W 0`
-- (sizeAt S 0 = S), so the restatement is `lvls-lin` at J = 0 and the
-- new count dominates the old one pointwise: every Instant-Height row
-- the product cleared, the level clears
count-gate : ∀ (S W D : ℕ) → 2 ≤ S →
  D * S * fCharge S W 0 ≤ lvls S W 0 D
count-gate S W D 2≤S =
  ≤-trans (≤-reflexive (*-assoc D S (fCharge S W 0))) (lvls-lin S W 0 D 2≤S)

-- and the registry the level reads dominates the old walk's threading
key : ∀ (S W R J d d̂ R′ : ℕ) → 2 ≤ S → 1 ≤ R →
  R′ ≤ regAt S R J → d ≤ d̂ →
  R′ + chargeAt S W 0 * suc d ≤ regAt S R (lvls S W J (suc d̂))
key S W R J d d̂ R′ 2≤S 1≤R hR′ hd =
  ≤-trans (+-mono-≤ hR′ (≤-trans (≤-reflexive (*-comm Q (suc d)))
                                 (*-monoˡ-≤ Q (s≤s hd))))
    (≤-trans (split J m)
             (regAt-mono {S} {S} {R} {R} {J + m} {lvls S W J (suc d̂)}
                ≤-refl ≤-refl (lvls-lin S W J (suc d̂) 2≤S)))
  where
  Q = chargeAt S W 0
  m = suc d̂ * Q
  1≤RS : 1 ≤ R * S
  1≤RS = ≤-trans 1≤R (≤-trans (≤-reflexive (sym (*-identityʳ R)))
                              (*-monoʳ-≤ R (≤-trans (s≤s z≤n) 2≤S)))
  eq : ∀ (r j m s : ℕ) → r * suc ((j + m) * s) ≡ r * suc (j * s) + m * (r * s)
  eq = solve 4 (λ r j m s → r :* (con 1 :+ (j :+ m) :* s)
                              := r :* (con 1 :+ j :* s) :+ m :* (r :* s))
             refl
  split : ∀ (j m : ℕ) → regAt S R j + m ≤ regAt S R (j + m)
  split j m = ≤-trans (+-monoʳ-≤ (regAt S R j)
                         (≤-trans (≤-reflexive (sym (*-identityʳ m)))
                                  (*-monoʳ-≤ m 1≤RS)))
                      (≤-reflexive (sym (eq R j m S)))

-- THE DOMINATION ITSELF.  `chargeAt S W 0` IS the old `chargeW` of the
-- entry caps and `regAt S R 0` IS the old entry registry, so this says
-- the level walk is pointwise above the registry walk it replaces
old≤new-cap : ∀ (g : ℕ) {S W R J R′ : ℕ} → 2 ≤ S → 1 ≤ R →
  R′ ≤ regAt S R J →
  dCap (chargeAt S W 0) g R′ ≤ dCapᶜ S W R g J
old≤new-walk : ∀ (g i i′ : ℕ) {S W R J R′ : ℕ} → 2 ≤ S → 1 ≤ R →
  R′ ≤ regAt S R J → i ≤ i′ →
  dWalk (chargeAt S W 0) g R′ i ≤ dWalkᶜ S W R g J i′

old≤new-cap zero    2≤S 1≤R hR = z≤n
old≤new-cap (suc g) {S} {W} {R} {J} {R′} 2≤S 1≤R hR =
  old≤new-walk g R′ (regAt S R J) 2≤S 1≤R hR hR

old≤new-walk g zero    i′       2≤S 1≤R hR hi       = z≤n
old≤new-walk g (suc i) zero     2≤S 1≤R hR ()
old≤new-walk g (suc i) (suc i′) {S} {W} {R} {J} {R′} 2≤S 1≤R hR (s≤s hi) =
  +-mono-≤ ih
    (s≤s (old≤new-cap g 2≤S 1≤R
            (key S W R J (dWalk (chargeAt S W 0) g R′ i)
                 (dWalkᶜ S W R g J i′) R′ 2≤S 1≤R hR ih)))
  where
  ih = old≤new-walk g i i′ 2≤S 1≤R hR hi

-- and at the entry level the two agree on their inputs, so the new cDel
-- dominates the old one AT THE SAME CAPS
old-cDel≤new-cDel : ∀ (S W R : ℕ) → 2 ≤ S → 1 ≤ R →
  dCap (S * suc (suc W * suc S)) (suc S) R ≤ dCapᶜ S W R (suc S) 0
old-cDel≤new-cDel S W R 2≤S 1≤R =
  old≤new-cap (suc S) 2≤S 1≤R (≤-reflexive (sym (*-identityʳ R)))
