------------------------------------------------------------------
-- THE RESIDUAL-BUDGET INVARIANT for `opIterD-budget-core`
-- (tier-1 #6, Op-Dominance.agda) — the design, derived 2026-08-06.
--
-- LEDGER CLASS: LANDING: Verify-Budget-Sufficient/Op-Dominance.agda
--
-- This file is the OUTSIDE-IN deliverable: the invariant is STATED,
-- its three step-estimates are PROVEN (dLvl-gain-sizeAt, jump-2step,
-- tail-fits — all three fell to the fLvl receipt, which carries
-- suc (widAt) * suc (sizeAt) per single step), and the assembly from
-- the invariant to the -core's exact conclusion TYPECHECKS.  The two
-- remaining postulates are the payment inductions themselves
-- (rounds-paid, climb-paid).
--
-- ══════════════════════════════════════════════════════════════
-- § THE TWO NORMAL FORMS the design rests on
-- ══════════════════════════════════════════════════════════════
--
-- CLIMB.  Unrolling opIterD's suc clause m times:
--
--     opIterD S W d k m J  =  TAIL^m ( (sLvlD k ∘ J₀)^m (J) )
--
-- where J₀(X) = suc (X + suc (sizeAt S X) * suc (sizeAt S X)) is the
-- per-round entry jump and TAIL(Y) = fIterD … (suc (widAt Y)) Y is the
-- per-round burst tail, already dominated in lvls-currency by the
-- PROVEN fIterD-lvls: TAIL(Y) ≤ lvls Y (suc (widAt Y)) =: G(Y).
-- So the whole climb is: m rounds, each = [jump, sub-climb at k−1
-- (sLvlD k X = opIterD (k−1) (suc (sizeAt S X)) X), tail].
--
-- BUDGET.  The PROVEN dWalkᶜ-front (Caps.agda:531) decomposes the walk
-- from the front: spending dCapᶜ (suc g) from level J is
--
--     iterate, once per position (regAt S R J of them):
--       [ ONE dLvl-step, then a FULL gas-g budget from the level
--         reached ]
--
-- — each position's recursive budget is evaluated at the level ALL
-- previous spending reached, so later positions start astronomically
-- above earlier ones.
--
-- ══════════════════════════════════════════════════════════════
-- § THE PAYMENT SCHEME (why the budget covers the climb)
-- ══════════════════════════════════════════════════════════════
--
-- Pay `opIterD k m` from a gas-g walk, sequentially across the walk's
-- positions — rounds NEVER share a position range:
--
--   · JUMP: two positions' direct dLvl-steps.  One dLvl from J ≥ X
--     gains ≥ sizeAt S J (it is 1 + sizeAt S J fLvlD-steps), so the
--     SECOND dLvl runs from a level ≥ sizeAt S X, where one more step
--     covers suc (sizeAt S X)² — `jump-2step` below.
--   · SUB-CLIMB (sLvlD k = opIterD (k−1) with m′ = suc (sizeAt S X)):
--     recursively paid from ONE position's gas-(g−1) budget.  The gas
--     guard suc k ≤ g descends in lockstep (suc (k−1) ≤ g−1).  The
--     m′-guard is restored by the boost: the sub-walk sits at a level
--     ≥ dLvl(J) ≥ sizeAt S X, so its regAt ≥ suc (level · S) ≥ m′ —
--     `dLvl-gain-sizeAt` below.  THIS is the resolution of the
--     m-vs-positions tension (m′ exponential in the level, positions
--     linear in it): positions are counted at the BOOSTED level.
--   · TAIL (suc (widAt Y) dLvl-steps, tower-many): paid from the NEXT
--     position's gas-(g−1) budget's LENGTH.  A gas-1 budget is only
--     regAt ≈ J·S long and CANNOT pay a tail; a gas-2 budget is a
--     tower of height regAt(J) > J ≥ height of widAt's tower —
--     `tail-fits` below.  So tails force 2 ≤ g−1 wherever they occur.
--
-- GAS ACCOUNTING, and it closes EXACTLY.  Paying opIterD k · needs
-- suc k ≤ g; the top climb has k ≤ S against cDel's gas suc S — zero
-- slack at k = S, which is presumably why the recurrence carries
-- suc (cSize) and not cSize.  The top-level walk at level 0 has only
-- regAt S R 0 = R positions (R = 1 is allowed!), so at the top the
-- entry (sLvlD k J₀′, itself a (k−1)-sub-climb) and all m rounds must
-- SEQUENCE INSIDE the single position's gas-S budget — its own walk
-- has regAt(dLvl 0) ≥ suc (S · dLvl 0) positions, plenty.  This is why
-- `climb-paid` (entry + rounds in one budget) is the top statement and
-- cannot be split into entry-budget + rounds-budget conjuncts.
--
-- CORNERS the eventual proof must respect:
--   · k = S: gas is exact, no headroom anywhere on the k-descent.
--   · S = 2: tails at the deepest gas level survive only because
--     suc m ≤ S forces m ≤ 1 there.
--   · d = 0 vs d ≥ 1: fLvlD's gains differ (fLvl + suc widAt vs the
--     sIterD walk); `dLvl-gain-sizeAt` must hold at BOTH, from the
--     (1 + sizeAt) step COUNT, not from per-step containment — the
--     depth-(d−1) machinery inside a depth-d L-step must never be
--     used to pay depth-d climbs (off-by-one in depth).
--   · The toolkit is largely PROVEN already: dWalkᶜ-front, dCapᶜ-mono/
--     dWalkᶜ-mono (mono in gas, level, positions, S, W, R), dLvl-mono,
--     sizeAt-mono, widAt-mono, lvls-add, lvls-mono, fIterD-lvls,
--     iterL-infl, 2≤dLvl.  The four estimates below are what is new.
------------------------------------------------------------------
module OpIterD-Invariant-Rehearsal where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; n≤1+n; m≤n+m; m≤m+n;
         *-identityˡ; *-identityʳ; *-monoˡ-≤; *-monoʳ-≤; *-mono-≤;
         +-suc; +-identityʳ; +-mono-≤; +-monoʳ-≤; <⇒≤; ^-monoˡ-≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Rx.Evaluator
  using (sizeAt; widAt; opIterD; sLvlD; dLvl; lvls; dCapᶜ; dWalkᶜ; regAt;
         fLvl; iterFold; foldStep)
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; cDel; cDel-body; sizeAt-mono; fLvl≤fLvlD;
         iterL-infl; 1≤regAt; dCapᶜ-mono; dWalkᶜ-mono; n<2^n)
open import Verify-Budget-Sufficient.Op-Dominance using (climb; fLvlD-le-dLvl)

-- the tail-closure: Y together with its burst tail, in lvls-currency.
-- fIterD-lvls (PROVEN, Op-Dominance) says every TAIL lands under G.
G : ℕ → ℕ → ℕ → ℕ → ℕ
G S W d Y = lvls S W d Y (suc (widAt S W Y))

------------------------------------------------------------------
-- § THE FOUR ESTIMATES (the genuinely new arithmetic)
------------------------------------------------------------------

-- One dLvl-step's gain covers sizeAt at any dominated level — PROVEN,
-- and by a stronger mechanism than first designed: no step-counting is
-- needed at all, because ONE fLvl receipt already carries the whole of
-- sizeAt.  fLvl S W J = J + suc (suc (widAt) * suc (sizeAt S J)) by
-- definition (fCharge), so sizeAt S J ≤ fLvl S W J outright; then
-- fLvl≤fLvlD (proven, .Caps) and fLvlD-le-dLvl (proven, Op-Dominance)
-- lift it through the ladder, and sizeAt-mono moves X up to J.
dLvl-gain-sizeAt : ∀ S W d X J → 2 ≤ S → X ≤ J →
  sizeAt S X ≤ dLvl S W d J
dLvl-gain-sizeAt S W d X J 2≤S hX =
  ≤-trans (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl hX)
  (≤-trans sizeAt≤fLvl
  (≤-trans (fLvl≤fLvlD S W d J) (fLvlD-le-dLvl S W d J)))
  where
  -- sizeAt S J ≤ suc (widAt) * suc (sizeAt S J) ≤ fCharge ≤ fLvl
  sizeAt≤fLvl : sizeAt S J ≤ fLvl S W J
  sizeAt≤fLvl =
    ≤-trans (n≤1+n (sizeAt S J))
    (≤-trans (≤-reflexive (sym (*-identityˡ (suc (sizeAt S J)))))
    (≤-trans (*-monoˡ-≤ (suc (sizeAt S J)) (s≤s (z≤n {widAt S W J})))
    (≤-trans (n≤1+n _)
             (m≤n+m (suc (suc (widAt S W J) * suc (sizeAt S J))) J))))

-- iterFold gains at least one per story (suc w ≤ foldStep S w = S^suc w
-- via n<2^n and ^-monoˡ-≤ — the same one-liner as Caps-Face's
-- suc≤foldStep, inlined to keep this probe off Caps-Face's clock), so
-- widAt S W A = iterFold S A W ≥ A + W ≥ A.
iterFold-gain : ∀ S k w → 2 ≤ S → k + w ≤ iterFold S k w
iterFold-gain S zero    w 2≤S = ≤-refl
iterFold-gain S (suc k) w 2≤S =
  ≤-trans (≤-reflexive (sym (+-suc k w)))
  (≤-trans (+-monoʳ-≤ k
             (≤-trans (<⇒≤ (n<2^n (suc w)))
                      (^-monoˡ-≤ (suc w) 2≤S)))
           (iterFold-gain S k (foldStep S w) 2≤S))

-- Two dLvl-steps cover the round's entry jump J₀(X) — PROVEN, again on
-- the fLvl receipt: with A = dLvl S W d J, the second step's receipt is
-- suc (suc (widAt A) * suc (sizeAt A)), and BOTH factors dominate
-- suc (sizeAt S X) — the width factor because widAt S W A ≥ A
-- (iterFold-gain) and A ≥ sizeAt S X (dLvl-gain-sizeAt), the size
-- factor by sizeAt-mono through X ≤ J ≤ A.  No 2^-lower-bound on
-- sizeAt is needed after all.
jump-2step : ∀ S W d X J → 2 ≤ S → X ≤ J →
  suc (X + suc (sizeAt S X) * suc (sizeAt S X)) ≤ dLvl S W d (dLvl S W d J)
jump-2step S W d X J 2≤S hX =
  ≤-trans (≤-reflexive (sym (+-suc X _)))
  (≤-trans (+-mono-≤ X≤A (s≤s product))
  (≤-trans (fLvl≤fLvlD S W d A) (fLvlD-le-dLvl S W d A)))
  where
  A : ℕ
  A = dLvl S W d J
  X≤A : X ≤ A
  X≤A = ≤-trans hX (iterL-infl S W d (suc (sizeAt S J)) J)
  f-wid : suc (sizeAt S X) ≤ suc (widAt S W A)
  f-wid = s≤s (≤-trans (dLvl-gain-sizeAt S W d X J 2≤S hX)
              (≤-trans (m≤m+n A W) (iterFold-gain S A W 2≤S)))
  f-size : suc (sizeAt S X) ≤ suc (sizeAt S A)
  f-size = s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl X≤A)
  product : suc (sizeAt S X) * suc (sizeAt S X)
              ≤ suc (widAt S W A) * suc (sizeAt S A)
  product = *-mono-≤ f-wid f-size

-- the gas-0 walk counts its positions and nothing else
dWalk0 : ∀ S W R d J i → dWalkᶜ S W R d 0 J i ≡ i
dWalk0 S W R d J zero    = refl
dWalk0 S W R d J (suc i) =
  trans (cong (_+ 1) (dWalk0 S W R d J i))
        (trans (+-suc i 0) (cong suc (+-identityʳ i)))

-- A gas-2 budget's LENGTH pays one tail — PROVEN, by a shorter route
-- than the tower-height comparison first designed: the walk's FIRST
-- position at gas 2 contributes suc (dCapᶜ gas-1 (dLvl J)) =
-- suc (regAt S R (dLvl J)) (dWalk0), and regAt at the boosted level
-- already dominates widAt S W J because ONE fLvl receipt at J carries
-- suc (widAt J) * suc (sizeAt J).  A gas-1 budget remains structurally
-- unable to pay a tail (its length is regAt at the UNBOOSTED level) —
-- the gas-headroom conjunct of the payment scheme stands.
tail-fits : ∀ S W d R J g → 2 ≤ S → 1 ≤ R → 2 ≤ g →
  suc (widAt S W J) ≤ dCapᶜ S W R d g J
tail-fits S W d R J g 2≤S 1≤R 2≤g =
  ≤-trans at2 (dCapᶜ-mono 2 g 2≤S ≤-refl ≤-refl ≤-refl 2≤g ≤-refl)
  where
  A : ℕ
  A = dLvl S W d J
  widAt≤A : widAt S W J ≤ A
  widAt≤A =
    ≤-trans (n≤1+n (widAt S W J))
    (≤-trans (≤-reflexive (sym (*-identityʳ (suc (widAt S W J)))))
    (≤-trans (*-monoʳ-≤ (suc (widAt S W J)) (s≤s (z≤n {sizeAt S J})))
    (≤-trans (n≤1+n _)
    (≤-trans (m≤n+m (suc (suc (widAt S W J) * suc (sizeAt S J))) J)
    (≤-trans (fLvl≤fLvlD S W d J) (fLvlD-le-dLvl S W d J))))))
  w≤reg : widAt S W J ≤ regAt S R A
  w≤reg =
    ≤-trans widAt≤A
    (≤-trans (≤-reflexive (sym (*-identityʳ A)))
    (≤-trans (*-monoʳ-≤ A (≤-trans (s≤s z≤n) 2≤S))
    (≤-trans (n≤1+n (A * S))
    (≤-trans (≤-reflexive (sym (*-identityˡ (suc (A * S)))))
             (*-monoˡ-≤ (suc (A * S)) 1≤R)))))
  at2 : suc (widAt S W J) ≤ dCapᶜ S W R d 2 J
  at2 =
    ≤-trans (s≤s w≤reg)
    (≤-trans (≤-reflexive (cong suc (sym (dWalk0 S W R d A (regAt S R A)))))
             (dWalkᶜ-mono 1 1 1 (regAt S R J) 2≤S ≤-refl ≤-refl ≤-refl
                          ≤-refl ≤-refl (1≤regAt S R J 1≤R)))

------------------------------------------------------------------
-- § THE INVARIANT (the recursive payment claim)
------------------------------------------------------------------

postulate
  -- Pay a k-climb of m rounds from the gas-g walk at level J, given:
  -- the gas covers the k-descent (suc k ≤ g), THIS level's positions
  -- cover the round count (m ≤ suc (J · S) ≤ regAt S R J via 1 ≤ R),
  -- and the climb-so-far — tail-closure included — sits below the
  -- walk's level (G X ≤ J).
  --
  -- PROOF PLAN (refined 2026-08-07): the induction is really over the
  -- POSITION index, via the sequencing frame that falls out of
  -- dWalkᶜ-front + lvls-add:
  --   walk-spend : lvls J (dWalkᶜ g J (suc i))
  --                  ≡ lvls J₁ (dWalkᶜ g J₁ i)
  --                where J₁ = lvls J (suc (dCapᶜ g (dLvl J)))
  -- — "one position = one dLvl-step plus a full gas-g sub-budget,
  -- then the walk RESTARTS from the level reached".  Chronological
  -- payment order per round is jump (2 positions, jump-2step with
  -- monotone slack), sub-climb (ONE position's gas-g sub-budget,
  -- recursively at (k−1); the m′-guard is restored at the sub-budget's
  -- boosted level by dLvl-gain-sizeAt), and the m TAILs cascade at the
  -- end, one position's sub-budget LENGTH each (tail-fits, needing the
  -- sub-budget gas ≥ 2).  Tail closure composes because
  -- G (TAIL Z) ≤ G (G Z) (fIterD-lvls + widAt-mono + lvls-mono), and
  -- G at a covered walk point is one more tail-fits application.
  -- ~4 positions per round; the position-form statement should carry
  -- `4 * m ≤ i` and be specialized to this level form at
  -- i = regAt S R J (whose guard bookkeeping vs 1 ≤ R is settled when
  -- proving, not here).
  rounds-paid : ∀ S W d R g k m X J → 2 ≤ S → 1 ≤ R →
    suc k ≤ g → m ≤ suc (J * S) → G S W d X ≤ J →
    G S W d (opIterD S W d k m X) ≤ lvls S W d J (dCapᶜ S W R d g J)

  -- The TOP form: entry (sLvlD k J₀′, a (k−1)-sub-climb from a level
  -- the walk has not yet reached) PLUS the m rounds, paid inside ONE
  -- budget — unsplittable because regAt S R 0 = R may be 1, so entry
  -- and rounds share the single top position's gas-S sub-budget.  Its
  -- eventual proof is one unrolling of the same scheme: dWalkᶜ-front
  -- once at level 0, then the entry as sub-climb #0 and `rounds-paid`
  -- for the rest.  Gas is generalized (suc S ≤ g) so the assembly
  -- below pins cDel's exact gas by cDel-body rather than by hand.
  climb-paid : ∀ S W d k m R g → 2 ≤ S → k ≤ S → suc m ≤ S → 1 ≤ R →
    suc S ≤ g →
    G S W d (climb S W d k m) ≤ lvls S W d 0 (dCapᶜ S W R d g 0)

------------------------------------------------------------------
-- § THE ASSEMBLY — the -core's exact conclusion from climb-paid.
-- This typechecking is the design's machine-checked receipt: the
-- invariant's statement FITS the postulate it is meant to replace
-- (cDel-body pins gas = suc S; record eta pins caps S W R's fields).
------------------------------------------------------------------

core-from-climb-paid : ∀ S W d k m R → 2 ≤ S → k ≤ S → suc m ≤ S → 1 ≤ R →
  lvls S W d (climb S W d k m) (suc (widAt S W (climb S W d k m)))
    ≤ lvls S W d 0 (cDel (caps S W R) d)
core-from-climb-paid S W d k m R 2≤S hk hm hR =
  ≤-trans
    (climb-paid S W d k m R (suc S) 2≤S hk hm hR ≤-refl)
    (≤-reflexive (cong (lvls S W d 0) (sym (cDel-body (caps S W R) d))))
