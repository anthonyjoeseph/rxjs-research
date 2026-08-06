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
-- pure arithmetic).  So the ENTIRE remaining question is the count bound
--   count-covers-tower : 3 + towerℕ sz ≤ sizeCount (capsAt e sl id) (capsH …)
-- (§ 3, POSTULATE).  Route and status in its header.  If it is FALSE, the
-- dry family is false as written and the anchor must be re-indexed; if it
-- holds, the family's headroom arithmetic is closed by tick-covers-instant.
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Battery-Tick-Headroom.agda &&
--   agda -i src -i probe probe/Battery-Tick-Headroom.agda
module Battery-Tick-Headroom where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans;
         *-monoˡ-≤; *-monoʳ-≤; +-mono-≤;
         *-assoc; *-comm; *-identityˡ; *-distribʳ-+;
         n≤1+n; m≤m+n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Prim using (towerℕ)
open import Rx.Exp  using (Ctx; Closed; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator using (sizeStep; iterSize)
open import Verify-Budget-Sufficient.Caps
  using (Caps; capsAt; capsH; sizeCount; 2≤capsAt-size)

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
-- § 3  THE ONE NAMED GAP — the count is tower-sized.
--
-- STATUS: POSTULATE, and NOT numerically probeable: `sizeCount` and `cDel`
-- are abstract, and even via their -body lemmas the value at any concrete
-- program is gated behind `capsH` = iterated `blowH`, which is abstract
-- AND tower-valued — the same three-seal lock as tier-1 #6.  Symbolic route
-- (recorded, unattempted):
--   sizeCount c d = lvls S W d 0 (cDel c d)          [sizeCount-body]
--   each dLvl step from level J climbs past sizeAt S J = iterSize S J S
--   ≥ 2^J (§ 1), so n dLvl steps from 0 climb a tower of height n;
--   cDel c d ≥ height needed follows from 1≤dCapᶜ-style positivity plus
--   the walk's regAt fan-out — the genuinely new part, same class as
--   opIterD-dominated (pure ℕ arithmetic, no evaluator).
-- If FALSE, the dry family is false as written (anchor re-index needed).
----------------------------------------------------------------------

postulate
  count-covers-tower : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    3 + towerℕ (sizeᵉ e + slotsSize sl)
      ≤ sizeCount (capsAt e sl id) (capsH e sl id)

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
--     (§ 2).  Both are real proofs over the actual recurrence, and the
--     assembly (§ 4) typechecks against the actual capsAt — so the dry
--     family's headroom question is now EXACTLY ONE inequality about the
--     count, not a design unknown.
-- (2) THE RESIDUAL, honestly labelled: count-covers-tower is a postulate,
--     abstract-locked against numeric probing, with its symbolic route
--     recorded in § 3.  It joins opIterD-dominated as the second member of
--     the "pure ℕ arithmetic over the sealed count machinery" class.
-- (3) DIRECTION OF THE EVIDENCE: j = sizeCount c d where each of the
--     count's own dLvl steps climbs through sizeAt S J ≥ 2^J — the count
--     machinery is BUILT from the same tower-climbing iterates as the
--     supply, with S = B ≥ 2 + sz.  The claim needs the count to reach
--     height ~towerℕ sz while its ingredients tower in S > sz; it leans
--     the right way, but that is an argument, and § 3 is where the proof
--     obligation now lives, greppable.
--
-- SHAPES COVERED: the statement level — supply chain proven for ALL e, sl,
-- id, symbolically.  NOT COVERED: the § 3 count bound (postulated), and the
-- demand MODEL (a′ ≤ 2a + v + 11, N ≤ towerℕ sz), which is the dry family's
-- own measured-not-proven content.
----------------------------------------------------------------------
