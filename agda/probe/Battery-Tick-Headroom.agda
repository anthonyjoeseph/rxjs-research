-- BATTERY: TICK HEADROOM — the tower-vs-tower comparison  (2026-08-06)
--
-- Phase 1b step 3.  Battery-Nesting-Escalation established that ONE instant
-- can grow value sizes by a TOWER in nesting depth (≤ sizeᵉ e).  The dry
-- family (Anchor-Dry-Probe.agda) survives as stated only if one caps tick —
-- the step from B = cSize (capsAt e sl id) to Ŝ = cSize (capsAt e sl (suc id))
-- — provides at least that much headroom.  This file decides the SHAPE of
-- that race and reduces it to one named count inequality.
--
-- THE SUPPLY CHAIN, read off the recurrence (all definitional):
--   capsAt e sl (suc id) = frameBlowup c (capsH e sl id)
--                        = frameStep (sizeCount c d) c        [c = capsAt id]
--   cSize thereof        = iterSize B j B,   j = sizeCount c (capsH e sl id)
--   sizeStep S s = S * suc (2 * s) ≥ 2s  (for S ≥ 1)
-- so ONE TICK MULTIPLIES BY AT LEAST 2^j (§ 1, proven).
--
-- THE DEMAND MODEL, from the measured recurrences (Battery-Obs-Growth,
-- Battery-Nesting-Escalation): within one instant, accumulators obey
-- a′ ≤ 2a + v + 11 with inputs v ≤ B and a₀ ≤ sizeᵉ e ≤ B, applied N times
-- with N ≤ towerℕ sz (count tower of height ≤ nesting depth < sz, where
-- sz = sizeᵉ e + slotsSize sl).  Hence one instant's sizes stay under
--   2^N · (2B + 11)  ≤  (2B + 12) · towerℕ (suc sz).
-- The model itself is the dry family's content (measured, not proven);
-- what THIS file settles is that the SUPPLY dominates that demand form.
--
-- THE VERDICT: the race resolves in favour of the caps — 2^j · B beats
-- (2B+12) · 2^(towerℕ sz) as soon as j ≥ 3 + towerℕ sz (§ 2, proven,
-- pure arithmetic), AND the count bound
--   count-covers-tower : 3 + towerℕ sz ≤ sizeCount (capsAt e sl id) (capsH …)
-- is PROVEN (§ 3, no postulates): lvls towers one exponential per step
-- (fLvlD is strictly inflationary, dLvl climbs past sizeAt ≥ 2^J) and its
-- budget cDel ≥ cReg (capsAt) ≥ 2 + sz.  So the dry family's headroom
-- arithmetic is CLOSED by tick-covers-instant, against the real recurrence,
-- with zero postulates in this file.
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Battery-Tick-Headroom.agda &&
--   agda -i src -i probe probe/Battery-Tick-Headroom.agda
module Battery-Tick-Headroom where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans;
         *-monoˡ-≤; *-monoʳ-≤; *-mono-≤; +-mono-≤; +-monoʳ-≤;
         *-assoc; *-comm; *-identityˡ; *-identityʳ; *-distribʳ-+;
         +-suc; +-comm; +-identityʳ;
         n≤1+n; m≤m+n; <⇒≤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Prim using (towerℕ)
open import Rx.Exp  using (Ctx; Closed; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Frame-Width using (entryCeil)
open import Rx.Evaluator
  using (sizeStep; iterSize; sizeAt; regAt; widAt; fCharge; fLvl;
         fLvlD; sIterD; iterL; dLvl; lvls; dCapᶜ; dWalkᶜ;
         fLvlD-0; fLvlD-suc; capsBase)
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; capsAt; capsH; sizeCount; sizeCount-body;
         cDel; cDel-body; frameBlowup;
         2≤capsAt-size; 2≤sizeCount; 2≤dLvl; lvls-mono; sIterD-zero≤; n<2^n)

----------------------------------------------------------------------
-- § 0  pow2 kit (local, to avoid stdlib name roulette)
----------------------------------------------------------------------

pow2-pos : ∀ n → 1 ≤ 2 ^ n
pow2-pos zero    = ≤-refl
pow2-pos (suc n) = ≤-trans (pow2-pos n) (m≤m+n (2 ^ n) (2 ^ n + 0))

pow2-mono : ∀ {m n} → m ≤ n → 2 ^ m ≤ 2 ^ n
pow2-mono {n = n} z≤n = pow2-pos n
pow2-mono (s≤s h)     = *-monoʳ-≤ 2 (pow2-mono h)

----------------------------------------------------------------------
-- § 1  ONE TICK MULTIPLIES BY AT LEAST 2^j — proven, no postulates.
--
-- sizeStep S s = S * suc (2 * s) ≥ 1 * suc (2s) ≥ 2s, so each of the j
-- iterations at least doubles.
----------------------------------------------------------------------

sizeStep-doubles : ∀ S s → 1 ≤ S → 2 * s ≤ sizeStep S s
sizeStep-doubles S s hS =
  ≤-trans (n≤1+n (2 * s))
    (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * s)))))
             (*-monoˡ-≤ (suc (2 * s)) hS))

iterSize-doubles : ∀ S j s → 1 ≤ S → (2 ^ j) * s ≤ iterSize S j s
iterSize-doubles S zero    s hS = ≤-reflexive (*-identityˡ s)
iterSize-doubles S (suc j) s hS =
  ≤-trans (≤-reflexive shuffle)
    (≤-trans (*-monoʳ-≤ (2 ^ j) (sizeStep-doubles S s hS))
             (iterSize-doubles S j (sizeStep S s) hS))
  where
    shuffle : (2 * 2 ^ j) * s ≡ 2 ^ j * (2 * s)
    shuffle = trans (cong (_* s) (*-comm 2 (2 ^ j)))
                    (*-assoc (2 ^ j) 2 s)

----------------------------------------------------------------------
-- § 2  THE RACE ARITHMETIC — proven, no postulates.
--
-- Demand (2B+12)·2^t is beaten by supply 2^j·B as soon as j ≥ 3 + t,
-- because 2B+12 ≤ 8B (for B ≥ 2) and 2^(3+t) = 8·2^t.
----------------------------------------------------------------------

headroom-arith : ∀ B t j → 2 ≤ B → 3 + t ≤ j →
  (2 * B + 12) * (2 ^ t) ≤ (2 ^ j) * B
headroom-arith B t j hB hj =
  ≤-trans demand≤8B2t
    (≤-trans (≤-reflexive rearrange)
             (*-monoˡ-≤ B (pow2-mono hj)))
  where
    -- 2B + 12 = 2B + 6·2 ≤ 2B + 6B = (2+6)·B = 8B
    coef : 2 * B + 12 ≤ 8 * B
    coef = ≤-trans (+-mono-≤ (≤-refl {2 * B}) (*-monoʳ-≤ 6 hB))
                   (≤-reflexive (sym (*-distribʳ-+ B 2 6)))

    demand≤8B2t : (2 * B + 12) * (2 ^ t) ≤ (8 * B) * (2 ^ t)
    demand≤8B2t = *-monoˡ-≤ (2 ^ t) coef

    -- 2^(3+t) unfolds to 2·(2·(2·2^t)), which is not defeq to 8·2^t
    eight : ∀ x → 2 * (2 * (2 * x)) ≡ 8 * x
    eight x = trans (cong (2 *_) (sym (*-assoc 2 2 x)))
                    (sym (*-assoc 2 4 x))

    -- (8·B)·2^t = 8·(B·2^t) = 8·(2^t·B) = (8·2^t)·B = 2^(3+t)·B
    rearrange : (8 * B) * (2 ^ t) ≡ (2 ^ (3 + t)) * B
    rearrange =
      trans (*-assoc 8 B (2 ^ t))
        (trans (cong (8 *_) (*-comm B (2 ^ t)))
          (trans (sym (*-assoc 8 (2 ^ t) B))
                 (cong (_* B) (sym (eight (2 ^ t))))))

----------------------------------------------------------------------
-- § 3  THE COUNT IS TOWER-SIZED — proven, no postulates.
--
-- The route the postulate's header recorded, executed:
--   sizeCount c d = lvls S W d 0 (cDel c d)            [sizeCount-body]
--   each lvls step applies dLvl, and dLvl S W d J ≥ suc (sizeAt S J) + J
--   with sizeAt S J ≥ 2^J (§ 1) — so n lvls steps from 0 climb a tower of
--   height n (lvls-tower below);
--   and cDel c d ≥ cReg c ≥ 2 + sz  (dWalkᶜ walks at least regAt S R 0 = R
--   positions, each adding ≥ 1; cReg's base is suc sz and frameStep only
--   multiplies it up — capsAt-reg below is the `capsAt-base-reg`-shaped
--   fact tier-1 #8's route note asked for, at ≥ 2 + sz).
-- Combining: sizeCount ≥ lvls 0 (2 + sz) ≥ 3 + towerℕ sz.
----------------------------------------------------------------------

-- (a) strictness: one fLvlD frame climbs by at least one.  Both clauses
-- factor through `fLvl S W J + suc (widAt S W J)` — d = 0 IS that value,
-- and the suc-d clause seeds sIterD with it via sIterD-zero≤.
fLvl-pad : ∀ S W J → suc J ≤ fLvl S W J + suc (widAt S W J)
fLvl-pad S W J =
  ≤-trans (s≤s (≤-trans (m≤m+n J (fCharge S W J))
                        (m≤m+n (fLvl S W J) (widAt S W J))))
          (≤-reflexive (sym (+-suc (fLvl S W J) (widAt S W J))))

fLvlD-strict : ∀ S W d J → suc J ≤ fLvlD S W d J
fLvlD-strict S W zero    J =
  ≤-trans (fLvl-pad S W J) (≤-reflexive (sym (fLvlD-0 S W J)))
fLvlD-strict S W (suc d) J =
  ≤-trans (≤-trans (fLvl-pad S W J)
                   (sIterD-zero≤ S W d (suc (sizeAt S (suc J)))
                                 (suc (widAt S W J)) (fLvl S W J)))
          (≤-reflexive (sym (fLvlD-suc S W d J)))

-- (b) so iterL advances by at least its budget, and dLvl by suc (sizeAt).
iterL-plus : ∀ S W d k J → k + J ≤ iterL S W d k J
iterL-plus S W d zero    J = ≤-refl
iterL-plus S W d (suc k) J =
  ≤-trans (≤-reflexive (sym (+-suc k J)))
    (≤-trans (+-monoʳ-≤ k (fLvlD-strict S W d J))
             (iterL-plus S W d k (fLvlD S W d J)))

dLvl-plus : ∀ S W d J → suc (sizeAt S J) + J ≤ dLvl S W d J
dLvl-plus S W d J = iterL-plus S W d (suc (sizeAt S J)) J

-- (c) each lvls step exponentiates: 2^J ≤ sizeAt S J, so n steps tower.
pow≤sizeAt : ∀ S J → 1 ≤ S → 2 ^ J ≤ sizeAt S J
pow≤sizeAt S J 1≤S =
  ≤-trans (≤-reflexive (sym (*-identityʳ (2 ^ J))))
    (≤-trans (*-monoʳ-≤ (2 ^ J) 1≤S) (iterSize-doubles S J S 1≤S))

lvls-tower : ∀ S W d n → 1 ≤ S → towerℕ n ≤ lvls S W d 0 (suc n)
lvls-tower S W d zero    1≤S = ≤-trans (s≤s z≤n) (2≤dLvl S W d 0)
lvls-tower S W d (suc n) 1≤S =
  ≤-trans (pow2-mono (lvls-tower S W d n 1≤S))
    (≤-trans (pow≤sizeAt S J 1≤S)
      (≤-trans (≤-trans (n≤1+n (sizeAt S J)) (m≤m+n (suc (sizeAt S J)) J))
               (dLvl-plus S W d J)))
  where J = lvls S W d 0 (suc n)

three-tower≤lvls : ∀ S W d sz → 1 ≤ S →
  3 + towerℕ sz ≤ lvls S W d 0 (suc (suc sz))
three-tower≤lvls S W d sz 1≤S =
  ≤-trans (s≤s step) (dLvl-plus S W d J)
  where
  J = lvls S W d 0 (suc sz)
  step : 2 + towerℕ sz ≤ sizeAt S J + J
  step = ≤-trans (≤-reflexive (+-comm 2 (towerℕ sz)))
    (+-mono-≤ (≤-trans (lvls-tower S W d sz 1≤S)
                       (≤-trans (<⇒≤ (n<2^n J)) (pow≤sizeAt S J 1≤S)))
              (2≤dLvl S W d (lvls S W d 0 sz)))

-- (d) the count's budget: cDel ≥ cReg (the walk visits regAt S R 0 = R
-- positions, each adding at least one), and cReg (capsAt) ≥ 2 + sz.
dWalkᶜ-ge : ∀ S W R d g J i → i ≤ dWalkᶜ S W R d g J i
dWalkᶜ-ge S W R d g J zero    = z≤n
dWalkᶜ-ge S W R d g J (suc i) =
  ≤-trans (≤-reflexive (sym (+-comm i 1)))
          (+-mono-≤ (dWalkᶜ-ge S W R d g J i) (s≤s z≤n))

cDel-ge-reg : ∀ (c : Caps) (d : ℕ) → Caps.cReg c ≤ cDel c d
cDel-ge-reg c d =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))
                   (dWalkᶜ-ge (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
                              (Caps.cSize c) 0
                              (regAt (Caps.cSize c) (Caps.cReg c) 0)))
          (≤-reflexive (sym (cDel-body c d)))

m≤m*2 : ∀ m → m ≤ m * 2
m≤m*2 m = ≤-trans (m≤m+n m m)
  (≤-reflexive (trans (cong (m +_) (sym (+-identityʳ m))) (*-comm 2 m)))

blow-reg-ge : ∀ (c : Caps) (d : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c * 2 ≤ Caps.cReg (frameBlowup c d)
blow-reg-ge c d 2≤S 1≤R =
  *-monoʳ-≤ (Caps.cReg c)
    (s≤s (*-mono-≤ (≤-trans (s≤s z≤n) (2≤sizeCount c d 2≤S 1≤R))
                   (≤-trans (s≤s z≤n) 2≤S)))

capsAt-reg : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 + (sizeᵉ e + slotsSize sl) ≤ Caps.cReg (capsAt e sl id)
capsAt-reg {n = n} e sl zero =
  ≤-trans (+-monoʳ-≤ 2 (m≤m*2 (sizeᵉ e + slotsSize sl)))
          (blow-reg-ge c₀ (capsBase e sl) (s≤s (s≤s z≤n)) (s≤s z≤n))
  where
  c₀ : Caps
  c₀ = caps (2 + sizeᵉ e + slotsSize sl) (suc (entryCeil n sl e))
            (suc (sizeᵉ e + slotsSize sl))
capsAt-reg e sl (suc id) =
  ≤-trans (capsAt-reg e sl id)
    (≤-trans (≤-reflexive (sym (*-identityʳ (Caps.cReg (capsAt e sl id)))))
             (*-monoʳ-≤ (Caps.cReg (capsAt e sl id)) (s≤s z≤n)))

-- (e) THE COUNT BOUND — a real definition, closing § 3.
count-covers-tower : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  3 + towerℕ (sizeᵉ e + slotsSize sl)
    ≤ sizeCount (capsAt e sl id) (capsH e sl id)
count-covers-tower e sl id =
  ≤-trans (≤-trans (three-tower≤lvls S W d sz 1≤S)
                   (lvls-mono (suc (suc sz)) (cDel c d)
                              (2≤capsAt-size e sl id) ≤-refl ≤-refl ≤-refl
                              (≤-trans (capsAt-reg e sl id)
                                       (cDel-ge-reg c d))))
          (≤-reflexive (sym (sizeCount-body c d)))
  where
  c  = capsAt e sl id
  d  = capsH e sl id
  S  = Caps.cSize c
  W  = Caps.cWid c
  sz = sizeᵉ e + slotsSize sl
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)

----------------------------------------------------------------------
-- § 4  THE ASSEMBLY — a real definition; the race closes from §§ 1-3.
--
-- Goal reduces DEFINITIONALLY: cSize (capsAt e sl (suc id)) is
-- iterSize B j B with B = cSize (capsAt e sl id), j = sizeCount c (capsH …)
-- (frameBlowup → frameStep → caps projection; sizeCount stays opaque, which
-- is fine — § 3 speaks about it opaquely too).
----------------------------------------------------------------------

tick-covers-instant : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  let B  = Caps.cSize (capsAt e sl id)
      sz = sizeᵉ e + slotsSize sl
  in (2 * B + 12) * towerℕ (suc sz) ≤ Caps.cSize (capsAt e sl (suc id))
tick-covers-instant e sl id =
  ≤-trans (headroom-arith B (towerℕ sz) j (2≤capsAt-size e sl id)
             (count-covers-tower e sl id))
          (iterSize-doubles B j B 1≤B)
  where
    B  = Caps.cSize (capsAt e sl id)
    sz = sizeᵉ e + slotsSize sl
    j  = sizeCount (capsAt e sl id) (capsH e sl id)
    1≤B : 1 ≤ B
    1≤B = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)

----------------------------------------------------------------------
-- § 5  VERDICT
--
-- (1) SUPPLY SHAPE PROVEN: one caps tick multiplies cSize by ≥ 2^j (§ 1),
--     and 2^j·B dominates the instant's tower demand once j ≥ 3 + towerℕ sz
--     (§ 2).  Both are real proofs over the actual recurrence.
-- (2) COUNT BOUND PROVEN (§ 3): sizeCount ≥ lvls 0 (2+sz) ≥ 3 + towerℕ sz,
--     from fLvlD's strict inflation (fLvl-pad through both clauses),
--     iterL/dLvl budget advancement, 2^J ≤ sizeAt S J, and
--     cDel ≥ cReg (capsAt) ≥ 2 + sz.  What the earlier draft postulated is
--     now a definition; this file carries ZERO postulates.
-- (3) BONUS WIRING NOTE: capsAt-reg is the `capsAt-base-reg`-shaped lemma
--     tier-1 #8's route note names as its sole missing sub-lemma (there
--     stated as `suc (sizeᵉ e + slotsSize sl) ≤ cReg (capsAt …)`; here
--     proven at the STRONGER 2 + sz).  When #8 is picked up, lift this
--     into Caps.agda rather than re-deriving it.
--
-- SHAPES COVERED: the statement level — supply chain AND count bound proven
-- for ALL e, sl, id, symbolically, zero postulates.  NOT COVERED: the demand
-- MODEL (a′ ≤ 2a + v + 11, N ≤ towerℕ sz), which is the dry family's own
-- measured-not-proven content — that is what the three dry postulates
-- assert, and it is the anchor's remaining open surface.
----------------------------------------------------------------------
