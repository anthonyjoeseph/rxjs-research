------------------------------------------------------------------
-- OP-BUDGET: the residual-budget invariant, PROVEN.
--
-- This is the arithmetic that `opIterD-budget` used to postulate
-- (tier-1 ledger #6, formerly `opIterD-budget-core` in Op-Dominance).
-- It is its own module because it is a lemma FAMILY consuming
-- Op-Dominance's results as finished facts — an import, not a
-- mutuality — and because Op-Dominance is imported far more widely
-- than this grind wants to recheck.
--
-- ══════════════════════════════════════════════════════════════
-- § THE TWO NORMAL FORMS the proof rests on
-- ══════════════════════════════════════════════════════════════
--
-- CLIMB.  Unrolling opIterD's suc clause m times:
--
--     opIterD S W d k m J  =  TAIL^m ( (sLvlD k ∘ J₀)^m (J) )
--
-- where J₀(X) = suc (X + suc (sizeAt S X) * suc (sizeAt S X)) is the
-- per-round entry jump and TAIL(Y) = fIterD … (suc (widAt Y)) Y is the
-- per-round burst tail, dominated in lvls-currency by Op-Dominance's
-- `fIterD-lvls`: TAIL(Y) ≤ lvls Y (suc (widAt Y)) =: G(Y).
--
-- BUDGET.  `dWalkᶜ-front` (Caps.agda) decomposes the walk from the
-- front: spending dCapᶜ (suc g) from level J is
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
-- § THE PAYMENT SCHEME, and its constants
-- ══════════════════════════════════════════════════════════════
--
-- One ROUND costs FIVE walk positions:
--   · positions 1–2, THE JUMP: two direct dLvl-steps.  One dLvl from
--     J ≥ X gains ≥ sizeAt S J, so the second runs from a level
--     ≥ sizeAt S X, where one more step covers suc (sizeAt S X)²
--     (`jump-2step`).
--   · position 3, THE G-ABSORB: a position spent as raw LENGTH cannot
--     double as the sub-climb's walk, so the entry's G-closure gets
--     its own (`G-absorb`).
--   · position 4, THE SUB-CLIMB: sLvlD k = opIterD (k−1) at
--     m′ = suc (sizeAt S X) is paid from this position's gas-(g−1)
--     sub-budget.  The m′-guard is restored by the BOOST: the
--     sub-walk sits at dLvl(level), so its regAt ≥ 5·m′ (`boost-5x`).
--     THIS is the resolution of the m-vs-positions tension — m′ is
--     exponential in the level and positions are linear in it, so
--     positions must be counted at the BOOSTED level.
--   · position 5, THE TAIL: paid from the next position's sub-budget
--     LENGTH.  A gas-1 budget is only regAt ≈ J·S long and provably
--     CANNOT pay a tail; a gas-2 budget is a tower of height regAt(J)
--     (`tail-fits`).  This is what forces the `2 +` in the guard.
--
-- GAS.  `walk-paid` needs `2 + k ≤ g`, and the k-descent preserves it
-- exactly ((g−1, k−1)).  The TOP (`climb-paid`) spends two more units:
-- one unfolding cDel's dCapᶜ into a walk, one descending into a
-- position because level 0 has only regAt S R 0 = R positions and
-- R MAY BE 1.  Hence the guard `3 + k ≤ S` — see § THE TOP FORM.
--
-- CORNERS respected: k at the guard boundary (gas is exact, no
-- headroom on the k-descent); S = 2 (tails at the deepest level
-- survive because suc m ≤ S forces m ≤ 1); d = 0 vs d ≥ 1 (fLvlD's
-- gains differ, so every estimate is read off the fLvl RECEIPT, which
-- carries suc (widAt) * suc (sizeAt) per single step, never off
-- per-step containment — the depth-(d−1) machinery inside a depth-d
-- L-step must never be used to pay depth-d climbs).
------------------------------------------------------------------
module Verify-Budget-Sufficient.Op-Budget where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; n≤1+n; m≤n+m; m≤m+n;
         *-identityˡ; *-identityʳ; *-monoˡ-≤; *-monoʳ-≤; *-mono-≤; *-suc;
         *-assoc; *-comm; ≤-pred; m≤m*n; +-assoc; +-comm;
         +-suc; +-identityʳ; +-mono-≤; +-monoʳ-≤; <⇒≤; ^-monoˡ-≤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Evaluator
  using (sizeAt; widAt; opIterD; sLvlD; dLvl; lvls; dCapᶜ; dWalkᶜ; regAt;
         fLvl; iterFold; foldStep; fIterD; opIterD-0; opIterD-suc;
         sLvlD-0; sLvlD-suc; fLvlD; fLvlD-0; fLvlD-suc; fIterD-0; fIterD-suc)
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; cDel; cDel-body; sizeAt-mono; widAt-mono; fLvl≤fLvlD;
         iterL-infl; 1≤regAt; dCapᶜ-mono; dWalkᶜ-mono; dWalkᶜ-front;
         lvls-mono; lvls-add; n<2^n; dLvl-mono; sLvlD-mono; 2≤dLvl)
open import Verify-Budget-Sufficient.Op-Dominance
  using (climb; fLvlD-le-dLvl; fIterD-lvls)

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
-- § THE GLUE — the identities the payment induction sequences with.
-- All PROVEN.  The load-bearing discovery: THE WALK VALUE AT p
-- POSITIONS IS THE p-TH RESTART LEVEL (walk-spend below composes
-- lvls-add over dWalkᶜ-front) — so a recursive payment's conclusion
-- glues directly into the next round's `G X ≤ J` hypothesis with no
-- residual bookkeeping.
------------------------------------------------------------------

-- spending never descends
lvls-infl : ∀ S W d J n → J ≤ lvls S W d J n
lvls-infl S W d J zero    = ≤-refl
lvls-infl S W d J (suc n) =
  ≤-trans (lvls-infl S W d J n)
          (iterL-infl S W d (suc (sizeAt S (lvls S W d J n))) (lvls S W d J n))

-- the tail-closure is monotone
G-mono : ∀ S W d {X Y} → 2 ≤ S → X ≤ Y → G S W d X ≤ G S W d Y
G-mono S W d 2≤S hXY =
  lvls-mono _ _ 2≤S ≤-refl ≤-refl hXY
    (s≤s (widAt-mono 2≤S ≤-refl ≤-refl hXY))

-- one TAIL costs at most one more G-closure
G-tail : ∀ S W d k Z → 2 ≤ S →
  G S W d (fIterD S W d k (suc (widAt S W Z)) Z) ≤ G S W d (G S W d Z)
G-tail S W d k Z 2≤S =
  G-mono S W d 2≤S (fIterD-lvls S W d k (suc (widAt S W Z)) Z 2≤S)

-- THE SEQUENCING FRAME: one position = one dLvl-step + a full gas-g
-- sub-budget, and the walk RESTARTS from the level reached.
-- (lvls S W d J 1 is definitionally dLvl S W d J.)
walk-spend : ∀ S W R d g J i →
  lvls S W d J (dWalkᶜ S W R d g J (suc i))
    ≡ lvls S W d (lvls S W d J (suc (dCapᶜ S W R d g (dLvl S W d J))))
                 (dWalkᶜ S W R d g
                   (lvls S W d J (suc (dCapᶜ S W R d g (dLvl S W d J)))) i)
walk-spend S W R d g J i =
  trans (cong (lvls S W d J) (dWalkᶜ-front S W R d g J i))
        (lvls-add S W d J
          (suc (dCapᶜ S W R d g (dLvl S W d J)))
          (dWalkᶜ S W R d g
            (lvls S W d J (suc (dCapᶜ S W R d g (dLvl S W d J)))) i))

-- the iterated sequencing frame: p + q positions from J = q positions
-- from the p-th restart level
walk-spend-many : ∀ S W R d g J p q →
  lvls S W d J (dWalkᶜ S W R d g J (p + q))
    ≡ lvls S W d (lvls S W d J (dWalkᶜ S W R d g J p))
                 (dWalkᶜ S W R d g (lvls S W d J (dWalkᶜ S W R d g J p)) q)
walk-spend-many S W R d g J zero    q = refl
walk-spend-many S W R d g J (suc p) q =
  trans (walk-spend S W R d g J (p + q))
  (trans (walk-spend-many S W R d g J₁ p q)
         (sym (cong (λ L → lvls S W d L (dWalkᶜ S W R d g L q))
                    (walk-spend S W R d g J p))))
  where
  J₁ = lvls S W d J (suc (dCapᶜ S W R d g (dLvl S W d J)))


------------------------------------------------------------------
-- § THE POSITION-FORM INDUCTION — REAL, MUTUAL, and the per-round
-- obligations are now PROVEN.  Uniform gas guard: 2 + k ≤ g (the
-- formalization sharpened the earlier {suc k ≤ g, 2 ≤ g} pair — the
-- tail headroom rides the k-descent, so the guard is one addition and
-- is preserved EXACTLY by the (g−1, k−1) sub-call).  Constants: one
-- round = 4 entry positions + 1 tail position, so m rounds cost 5m.
------------------------------------------------------------------

-- the first position's restart clears one dLvl-step
restart-ge-dLvl : ∀ S W R d g J →
  dLvl S W d J ≤ lvls S W d J (dWalkᶜ S W R d g J 1)
restart-ge-dLvl S W R d g J =
  ≤-trans (lvls-infl S W d (dLvl S W d J) (dCapᶜ S W R d g (dLvl S W d J)))
          (≤-reflexive (sym (lvls-add S W d J 1
                              (dCapᶜ S W R d g (dLvl S W d J)))))

-- the G-closure of a level is absorbed by one position's sub-budget
-- length (this is what forces 2 ≤ g — a gas-1 sub-budget cannot pay
-- a widAt-sized count)
G-absorb : ∀ S W R d g V → 2 ≤ S → 1 ≤ R → 2 ≤ g →
  G S W d V ≤ lvls S W d V (dWalkᶜ S W R d g V 1)
G-absorb S W R d g V 2≤S 1≤R 2≤g =
  lvls-mono _ _ 2≤S ≤-refl ≤-refl ≤-refl
    (s≤s (≤-trans (widAt-mono 2≤S ≤-refl ≤-refl
                    (iterL-infl S W d (suc (sizeAt S V)) V))
         (≤-trans (n≤1+n (widAt S W (dLvl S W d V)))
                  (tail-fits S W d R (dLvl S W d V) g 2≤S 1≤R 2≤g))))

-- (c) ONE TAIL — PROVEN: given the recursive payment's conclusion at
-- the i-th restart level V, one more position absorbs the round's
-- TAIL (G-tail, G-mono, G-absorb, walk-spend-many).
round-tail-glue : ∀ S W R d g k Z J i → 2 ≤ S → 1 ≤ R → 2 ≤ g →
  G S W d Z ≤ lvls S W d J (dWalkᶜ S W R d g J i) →
  G S W d (fIterD S W d k (suc (widAt S W Z)) Z)
    ≤ lvls S W d J (dWalkᶜ S W R d g J (suc i))
round-tail-glue S W R d g k Z J i 2≤S 1≤R 2≤g hZ =
  ≤-trans (G-tail S W d k Z 2≤S)
  (≤-trans (G-mono S W d 2≤S hZ)
  (≤-trans (G-absorb S W R d g (lvls S W d J (dWalkᶜ S W R d g J i))
              2≤S 1≤R 2≤g)
  (≤-trans (≤-reflexive (sym (walk-spend-many S W R d g J i 1)))
           (≤-reflexive (cong (λ p → lvls S W d J (dWalkᶜ S W R d g J p))
                              (trans (+-suc i 0) (cong suc (+-identityʳ i))))))))

-- the boost: five sub-rounds' worth of positions exist at one
-- dLvl-boosted level — the fLvl receipt's width factor is ≥ 3 once the
-- level clears 2, so dLvl Q ≥ 3·suc (sizeAt S Y), and regAt multiplies
-- by S ≥ 2 and R ≥ 1 on top
boost-5x : ∀ S W R d Y Q → 2 ≤ S → 1 ≤ R → 2 ≤ Q → Y ≤ Q →
  5 * suc (sizeAt S Y) ≤ regAt S R (dLvl S W d Q)
boost-5x S W R d Y Q 2≤S 1≤R 2≤Q hY =
  ≤-trans (*-monoˡ-≤ (suc (sizeAt S Y)) 5≤6)
  (≤-trans (≤-reflexive (*-assoc 2 3 (suc (sizeAt S Y))))
  (≤-trans (*-monoʳ-≤ 2 three-x≤dLvl)
  (≤-trans (*-monoˡ-≤ (dLvl S W d Q) 2≤S)
  (≤-trans (≤-reflexive (*-comm S (dLvl S W d Q)))
  (≤-trans (n≤1+n (dLvl S W d Q * S))
  (≤-trans (≤-reflexive (sym (*-identityˡ (suc (dLvl S W d Q * S)))))
           (*-monoˡ-≤ (suc (dLvl S W d Q * S)) 1≤R)))))))
  where
  5≤6 : 5 ≤ 6
  5≤6 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
  3≤sw : 3 ≤ suc (widAt S W Q)
  3≤sw = s≤s (≤-trans 2≤Q
               (≤-trans (m≤m+n Q W) (iterFold-gain S Q W 2≤S)))
  three-x≤dLvl : 3 * suc (sizeAt S Y) ≤ dLvl S W d Q
  three-x≤dLvl =
    ≤-trans (*-mono-≤ 3≤sw
              (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl hY)))
    (≤-trans (n≤1+n _)
    (≤-trans (m≤n+m (suc (suc (widAt S W Q) * suc (sizeAt S Q))) Q)
    (≤-trans (fLvl≤fLvlD S W d Q) (fLvlD-le-dLvl S W d Q))))

mutual
  -- THE POSITION-FORM INVARIANT: m rounds cost 5m positions; the walk
  -- value at p positions IS the p-th restart level (walk-spend), so
  -- each conclusion is the next call's hypothesis verbatim.
  walk-paid : ∀ S W R d g k m X J → 2 ≤ S → 1 ≤ R →
    2 + k ≤ g →
    G S W d X ≤ J →
    G S W d (opIterD S W d k m X)
      ≤ lvls S W d J (dWalkᶜ S W R d g J (5 * m))
  walk-paid S W R d g k zero X J 2≤S 1≤R hkg hX =
    ≤-trans (G-mono S W d 2≤S (≤-reflexive (opIterD-0 S W d k X))) hX
  walk-paid S W R d g k (suc m) X J 2≤S 1≤R hkg hX =
    ≤-trans (G-mono S W d 2≤S (≤-reflexive (opIterD-suc S W d k m X)))
    (≤-trans tail-step
             (≤-reflexive
               (cong (λ i → lvls S W d J (dWalkᶜ S W R d g J i)) count-eq)))
    where
    J₀X = suc (X + suc (sizeAt S X) * suc (sizeAt S X))
    X₁  = sLvlD S W d k J₀X
    Z   = opIterD S W d k m X₁
    P₄  = lvls S W d J (dWalkᶜ S W R d g J 4)

    entry : G S W d X₁ ≤ P₄
    entry = round-entry-paid S W R d g k X J 2≤S 1≤R hkg
              (≤-trans (lvls-infl S W d X (suc (widAt S W X))) hX)

    rec : G S W d Z ≤ lvls S W d P₄ (dWalkᶜ S W R d g P₄ (5 * m))
    rec = walk-paid S W R d g k m X₁ P₄ 2≤S 1≤R hkg entry

    rec′ : G S W d Z ≤ lvls S W d J (dWalkᶜ S W R d g J (4 + 5 * m))
    rec′ = ≤-trans rec
             (≤-reflexive (sym (walk-spend-many S W R d g J 4 (5 * m))))

    tail-step : G S W d (fIterD S W d k (suc (widAt S W Z)) Z)
                  ≤ lvls S W d J (dWalkᶜ S W R d g J (suc (4 + 5 * m)))
    tail-step = round-tail-glue S W R d g k Z J (4 + 5 * m) 2≤S 1≤R
                  (≤-trans (m≤m+n 2 k) hkg) rec′

    count-eq : suc (4 + 5 * m) ≡ 5 * suc m
    count-eq = sym (*-suc 5 m)

  -- (a) ONE ROUND'S ENTRY — PROVEN, mutual with walk-paid: positions
  -- 1-2 clear the jump (jump-2step through two restarts), position 3
  -- absorbs G (J₀ X) (G-absorb — the sub-call's hypothesis is
  -- G-closed, and a position spent as raw length cannot double as the
  -- sub-climb's walk), and position 4's sub-budget hosts the
  -- (g−1, k−1) sub-climb, its 5m′ positions fitting under the full
  -- regAt at the boosted level by boost-5x; the position-4 restart
  -- P₄ ≡ lvls (dLvl P₃) (dCapᶜ g (dLvl P₃)) receives it exactly.
  -- NOTE the hypothesis is the BARE `X ≤ J`, not the G-closed form:
  -- formalizing showed the entry never spends the closure (it only
  -- needs X under the anchor, then jumps through two restarts).  That
  -- matters at the TOP, where X ≡ 0 and `G S W d 0 ≤ J` is NOT free
  -- while `0 ≤ J` is — see climb-paid below.
  round-entry-paid : ∀ S W R d g k X J → 2 ≤ S → 1 ≤ R →
    2 + k ≤ g →
    X ≤ J →
    G S W d (sLvlD S W d k
              (suc (X + suc (sizeAt S X) * suc (sizeAt S X))))
      ≤ lvls S W d J (dWalkᶜ S W R d g J 4)
  round-entry-paid S W R d zero    k X J 2≤S 1≤R () hX
  round-entry-paid S W R d (suc g′) zero X J 2≤S 1≤R hkg hX =
    ≤-trans (G-mono S W d 2≤S (≤-reflexive (sLvlD-0 S W d J₀X)))
    (≤-trans GJ₀≤P₃
    (≤-trans (lvls-infl S W d P₃ (dWalkᶜ S W R d (suc g′) P₃ 1))
             (≤-reflexive (sym (walk-spend-many S W R d (suc g′) J 3 1)))))
    where
    g = suc g′
    J₀X = suc (X + suc (sizeAt S X) * suc (sizeAt S X))
    P₁ = lvls S W d J (dWalkᶜ S W R d g J 1)
    P₂ = lvls S W d J (dWalkᶜ S W R d g J 2)
    P₃ = lvls S W d J (dWalkᶜ S W R d g J 3)

    X≤J : X ≤ J
    X≤J = hX

    dd≤P₂ : dLvl S W d (dLvl S W d J) ≤ P₂
    dd≤P₂ = ≤-trans (dLvl-mono 2≤S ≤-refl ≤-refl
                      (restart-ge-dLvl S W R d g J))
            (≤-trans (restart-ge-dLvl S W R d g P₁)
                     (≤-reflexive (sym (walk-spend-many S W R d g J 1 1))))

    jump : J₀X ≤ P₂
    jump = ≤-trans (jump-2step S W d X J 2≤S X≤J) dd≤P₂

    GJ₀≤P₃ : G S W d J₀X ≤ P₃
    GJ₀≤P₃ = ≤-trans (G-mono S W d 2≤S jump)
             (≤-trans (G-absorb S W R d g P₂ 2≤S 1≤R
                         (≤-trans (m≤m+n 2 zero) hkg))
                      (≤-reflexive (sym (walk-spend-many S W R d g J 2 1))))
  round-entry-paid S W R d (suc g′) (suc k′) X J 2≤S 1≤R hkg hX =
    ≤-trans (G-mono S W d 2≤S (≤-reflexive (sLvlD-suc S W d k′ J₀X)))
    (≤-trans sub-paid (≤-reflexive (sym P₄≡)))
    where
    g = suc g′
    k = suc k′
    J₀X = suc (X + suc (sizeAt S X) * suc (sizeAt S X))
    m′ = suc (sizeAt S J₀X)
    P₁ = lvls S W d J (dWalkᶜ S W R d g J 1)
    P₂ = lvls S W d J (dWalkᶜ S W R d g J 2)
    P₃ = lvls S W d J (dWalkᶜ S W R d g J 3)
    P₄ = lvls S W d J (dWalkᶜ S W R d g J 4)
    Pw = dLvl S W d P₃

    X≤J : X ≤ J
    X≤J = hX

    2≤g : 2 ≤ g
    2≤g = ≤-trans (m≤m+n 2 k) hkg

    dd≤P₂ : dLvl S W d (dLvl S W d J) ≤ P₂
    dd≤P₂ = ≤-trans (dLvl-mono 2≤S ≤-refl ≤-refl
                      (restart-ge-dLvl S W R d g J))
            (≤-trans (restart-ge-dLvl S W R d g P₁)
                     (≤-reflexive (sym (walk-spend-many S W R d g J 1 1))))

    jump : J₀X ≤ P₂
    jump = ≤-trans (jump-2step S W d X J 2≤S X≤J) dd≤P₂

    P₂≤P₃ : P₂ ≤ P₃
    P₂≤P₃ = lvls-mono (dWalkᶜ S W R d g J 2) (dWalkᶜ S W R d g J 3)
              2≤S ≤-refl ≤-refl ≤-refl
              (dWalkᶜ-mono {S} {S} {W} {W} {R} {R} {J} {J} {d}
                g g 2 3 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                (s≤s (s≤s z≤n)))

    GJ₀≤P₃ : G S W d J₀X ≤ P₃
    GJ₀≤P₃ = ≤-trans (G-mono S W d 2≤S jump)
             (≤-trans (G-absorb S W R d g P₂ 2≤S 1≤R 2≤g)
                      (≤-reflexive (sym (walk-spend-many S W R d g J 2 1))))

    2≤P₃ : 2 ≤ P₃
    2≤P₃ = ≤-trans (2≤dLvl S W d (dLvl S W d J))
                   (≤-trans dd≤P₂ P₂≤P₃)

    -- hkg : suc (suc (suc k′)) ≤ suc g′, so one s≤s peel IS 2 + k′ ≤ g′
    hkg′ : 2 + k′ ≤ g′
    hkg′ = ≤-pred hkg

    rec-sub : G S W d (opIterD S W d k′ m′ J₀X)
                ≤ lvls S W d Pw (dWalkᶜ S W R d g′ Pw (5 * m′))
    rec-sub = walk-paid S W R d g′ k′ m′ J₀X Pw 2≤S 1≤R hkg′
                (≤-trans GJ₀≤P₃ (iterL-infl S W d (suc (sizeAt S P₃)) P₃))

    fit : dWalkᶜ S W R d g′ Pw (5 * m′) ≤ dWalkᶜ S W R d g′ Pw (regAt S R Pw)
    fit = dWalkᶜ-mono g′ g′ (5 * m′) (regAt S R Pw) 2≤S ≤-refl ≤-refl ≤-refl
            ≤-refl ≤-refl
            (boost-5x S W R d J₀X P₃ 2≤S 1≤R 2≤P₃
              (≤-trans jump P₂≤P₃))

    sub-paid : G S W d (opIterD S W d k′ m′ J₀X)
                 ≤ lvls S W d Pw (dCapᶜ S W R d g Pw)
    sub-paid = ≤-trans rec-sub
                 (lvls-mono _ _ 2≤S ≤-refl ≤-refl ≤-refl fit)

    P₄≡ : P₄ ≡ lvls S W d Pw (dCapᶜ S W R d g Pw)
    P₄≡ = trans (walk-spend-many S W R d g J 3 1)
                (lvls-add S W d P₃ 1 (dCapᶜ S W R d g Pw))

------------------------------------------------------------------
-- § THE TOP FORM — PROVEN 2026-08-07, and the formalization PINS THE
-- GAS CORNER EXACTLY: the guard the proof needs is `3 + k ≤ S`, not
-- `k ≤ S`.  This is the finding the rehearsal exists to produce, and
-- it is now a number rather than an estimate.
--
-- THE ARITHMETIC, all four gas units accounted:
--   cDel's gas is `suc S` (dCapᶜ S W R d (suc S) 0).  One unit is spent
--   unfolding dCapᶜ into the top WALK (gas index S, level 0).  That
--   walk has regAt S R 0 = R positions and R MAY BE 1, so the climb
--   cannot be sequenced there; it must descend into one position's
--   sub-budget — a SECOND unit — landing on a walk of gas index S−1 at
--   level A₁ = dLvl S W d 0, where positions are plentiful
--   (regAt S R A₁ ≥ suc (A₁·S) ≥ 5·S, since 5 ≤ A₁ — `5≤dLvl0`).
--   walk-paid on that walk needs `2 + k ≤ S − 1`.  Hence 3 + k ≤ S.
--
-- The `2` inside walk-paid's own guard is irreducible: at k = 0 the
-- entry still spends G-absorb, and G-absorb rests on tail-fits, which
-- PROVABLY cannot be paid by a gas-1 sub-budget.  The two descents are
-- likewise forced (dCapᶜ → walk, and level-0 → a level with positions).
-- So `3 + k ≤ S` is not slack this scheme happens to want; it is what
-- the recurrence costs.
--
-- CONSEQUENCE FOR SRC — a statement repair on `opIterD-budget-core`
-- and `opIterD-dominated`, whose guard `k ≤ S` becomes `3 + k ≤ S`,
-- and thence on `sub-charge-capsOK-lift-core`'s nestOK premise
-- (`nest b sl cs ≤ cSize c` becomes `3 + nest b sl cs ≤ cSize c`).
-- That premise is threaded, not derived, so the obligation lands on
-- nestOK's suppliers, where it is PLAUSIBLY FREE: cSize (capsAt e sl
-- id) is `frameBlowup` applied to `caps (2 + sizeᵉ e + slotsSize sl)
-- …`, i.e. an iterSize tower ABOVE 2 + sizeᵉ e + slotsSize sl, while
-- nest≤ bounds nest by sizeᵉ + slotsSize.  It is a repair to make
-- deliberately and to discharge as a NAMED obligation, never to
-- absorb silently.
------------------------------------------------------------------

-- The first descent needs a level with room.  `2≤dLvl` is not enough
-- (5·S positions are wanted against suc (A₁·S) available), so unroll
-- iterL TWICE: dLvl S W d 0 = iterL S W d (suc (sizeAt S 0)) 0 and
-- sizeAt S 0 = S ≥ 2, so at least two fLvlD-steps run, the first
-- clearing 4 (fLvl S W 0 = suc (suc W * suc S) ≥ 4) and the second
-- adding its own fCharge ≥ 2.
5≤dLvl0 : ∀ S W d → 2 ≤ S → 5 ≤ dLvl S W d 0
5≤dLvl0 zero          W d ()
5≤dLvl0 (suc zero)    W d (s≤s ())
5≤dLvl0 (suc (suc s)) W d 2≤S =
  ≤-trans 5≤6 (≤-trans 6≤F₁ (iterL-infl S W d (suc s) F₁))
  where
  S = suc (suc s)
  F₀ = fLvlD S W d 0
  F₁ = fLvlD S W d F₀

  5≤6 : 5 ≤ 6
  5≤6 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

  -- fLvl S W 0 = suc (suc W * suc S), and suc W * suc S ≥ 1 * 3
  4≤F₀ : 4 ≤ F₀
  4≤F₀ = ≤-trans (s≤s (≤-trans (≤-reflexive (sym (*-identityˡ 3)))
                               (*-mono-≤ (s≤s (z≤n {W}))
                                         (s≤s (s≤s (s≤s (z≤n {s})))))))
                 (fLvl≤fLvlD S W d 0)

  -- one more step costs its own fCharge, which is ≥ suc (1 * 1)
  2≤charge : 2 ≤ suc (suc (widAt S W F₀) * suc (sizeAt S F₀))
  2≤charge = s≤s (≤-trans (≤-reflexive (sym (*-identityˡ 1)))
                          (*-mono-≤ (s≤s (z≤n {widAt S W F₀}))
                                    (s≤s (z≤n {sizeAt S F₀}))))

  6≤F₁ : 6 ≤ F₁
  6≤F₁ = ≤-trans (+-mono-≤ 4≤F₀ 2≤charge) (fLvl≤fLvlD S W d F₀)

-- the descended walk has room for the entry's 4 positions and the
-- m rounds' 5m
top-positions : ∀ S W R d m → 2 ≤ S → 1 ≤ R → suc m ≤ S →
  4 + 5 * m ≤ regAt S R (dLvl S W d 0)
top-positions S W R d m 2≤S 1≤R hm =
  ≤-trans (n≤1+n (4 + 5 * m))
  (≤-trans (≤-reflexive (sym (*-suc 5 m)))
  (≤-trans (*-monoʳ-≤ 5 hm)
  (≤-trans (*-monoˡ-≤ S (5≤dLvl0 S W d 2≤S))
  (≤-trans (n≤1+n (dLvl S W d 0 * S))
  (≤-trans (≤-reflexive (sym (*-identityˡ (suc (dLvl S W d 0 * S)))))
           (*-monoˡ-≤ (suc (dLvl S W d 0 * S)) 1≤R))))))

-- THE TOP UNROLLING, at cDel's own gas.
climb-paid-at : ∀ S W d k m R → 2 ≤ S → 3 + k ≤ S → suc m ≤ S → 1 ≤ R →
  G S W d (climb S W d k m) ≤ lvls S W d 0 (dCapᶜ S W R d (suc S) 0)
climb-paid-at zero      W d k m R ()  hk hm hR
climb-paid-at (suc S′)  W d k m R 2≤S hk hm hR = ≤-trans step2 step1
  where
  S  = suc S′
  A₁ = dLvl S W d 0
  X₁ = sLvlD S W d k (suc (suc (sizeAt S 0) * suc (sizeAt S 0)))
  Q₁ = lvls S W d A₁ (dCapᶜ S W R d S A₁)
  P₄ = lvls S W d A₁ (dWalkᶜ S W R d S′ A₁ 4)

  -- ONE top position lands exactly on Q₁ (walk-spend at i = 0, then
  -- lvls-add splitting the leading dLvl-step off the restart count)
  one-pos : lvls S W d 0 (dWalkᶜ S W R d S 0 1) ≡ Q₁
  one-pos = trans (walk-spend S W R d S 0 0)
                  (lvls-add S W d 0 1 (dCapᶜ S W R d S A₁))

  step1 : Q₁ ≤ lvls S W d 0 (dCapᶜ S W R d (suc S) 0)
  step1 =
    ≤-trans (≤-reflexive (sym one-pos))
            (lvls-mono (dWalkᶜ S W R d S 0 1) (dWalkᶜ S W R d S 0 (regAt S R 0))
               2≤S ≤-refl ≤-refl ≤-refl
               (dWalkᶜ-mono {S} {S} {W} {W} {R} {R} {0} {0} {d}
                  S S 1 (regAt S R 0) 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                  (1≤regAt S R 0 hR)))

  hkg : 2 + k ≤ S′
  hkg = ≤-pred hk

  -- at the top X ≡ 0, so the entry's hypothesis is `z≤n` — this is the
  -- one place the bare-X form of round-entry-paid earns its keep
  entry : G S W d X₁ ≤ P₄
  entry = round-entry-paid S W R d S′ k 0 A₁ 2≤S hR hkg z≤n

  rounds : G S W d (opIterD S W d k m X₁)
             ≤ lvls S W d P₄ (dWalkᶜ S W R d S′ P₄ (5 * m))
  rounds = walk-paid S W R d S′ k m X₁ P₄ 2≤S hR hkg entry

  rounds′ : G S W d (opIterD S W d k m X₁)
              ≤ lvls S W d A₁ (dWalkᶜ S W R d S′ A₁ (4 + 5 * m))
  rounds′ = ≤-trans rounds
              (≤-reflexive (sym (walk-spend-many S W R d S′ A₁ 4 (5 * m))))

  step2 : G S W d (climb S W d k m) ≤ Q₁
  step2 =
    ≤-trans rounds′
            (lvls-mono (dWalkᶜ S W R d S′ A₁ (4 + 5 * m))
                       (dWalkᶜ S W R d S′ A₁ (regAt S R A₁))
               2≤S ≤-refl ≤-refl ≤-refl
               (dWalkᶜ-mono {S} {S} {W} {W} {R} {R} {A₁} {A₁} {d}
                  S′ S′ (4 + 5 * m) (regAt S R A₁)
                  2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                  (top-positions S W R d m 2≤S hR hm)))

climb-paid : ∀ S W d k m R g → 2 ≤ S → 3 + k ≤ S → suc m ≤ S → 1 ≤ R →
  suc S ≤ g →
  G S W d (climb S W d k m) ≤ lvls S W d 0 (dCapᶜ S W R d g 0)
climb-paid S W d k m R g 2≤S hk hm hR hg =
  ≤-trans (climb-paid-at S W d k m R 2≤S hk hm hR)
          (lvls-mono (dCapᶜ S W R d (suc S) 0) (dCapᶜ S W R d g 0)
             2≤S ≤-refl ≤-refl ≤-refl
             (dCapᶜ-mono {S} {S} {W} {W} {R} {R} {0} {0} {d}
                (suc S) g 2≤S ≤-refl ≤-refl ≤-refl hg ≤-refl))

------------------------------------------------------------------
-- § THE ASSEMBLY — route steps (a)+(b), which used to be the
-- monolithic postulate `opIterD-budget-core`.  cDel-body pins gas at
-- suc S; record eta pins `caps S W R`'s fields.
--
-- `1 ≤ R` IS LOAD-BEARING, and the statement without it is FALSE —
-- machine-refuted 2026-08-06, probe/OpIterD-Budget-Probe.agda §1
-- (`opIterD-budget-R0-false`, a proven → ⊥).  At R = 0 the registry
-- walk is empty (`regAt S 0 J = 0 * suc (J * S) = 0`), so
-- `cDel (caps S W 0) d = 0` and the RHS collapses to
-- `lvls S W d 0 0 = 0`; but the LHS is a `dLvl` application and
-- `2≤dLvl` holds unconditionally, so the claim read `2 ≤ 0`.
------------------------------------------------------------------

opIterD-budget : ∀ S W d k m R → 2 ≤ S → 3 + k ≤ S → suc m ≤ S → 1 ≤ R →
  lvls S W d (climb S W d k m) (suc (widAt S W (climb S W d k m)))
    ≤ lvls S W d 0 (cDel (caps S W R) d)
opIterD-budget S W d k m R 2≤S hk hm hR =
  ≤-trans
    (climb-paid S W d k m R (suc S) 2≤S hk hm hR ≤-refl)
    (≤-reflexive (cong (lvls S W d 0) (sym (cDel-body (caps S W R) d))))

-- THE CONSUMER-FACING FORM.  m = 0 is real (opIterD-0 gives 0 on the
-- left); m = suc _ is the proven fIterD tail (fIterD-lvls) over the
-- now-proven climb budget.
--
-- `1 ≤ R` is inherited from opIterD-budget, and only the suc case
-- spends it: at m = 0 the LHS is 0 by opIterD-0, so the R = 0
-- collapse is harmless there.  It is carried in the signature
-- regardless, because the suc case needs it and a hypothesis that
-- appears in one clause belongs to the statement.
opIterD-dominated : ∀ S W d k m R → 2 ≤ S → 3 + k ≤ S → m ≤ S → 1 ≤ R →
  opIterD S W d k m 0 ≤ lvls S W d 0 (cDel (caps S W R) d)
opIterD-dominated S W d k zero    R 2≤S hk hm hR =
  ≤-trans (≤-reflexive (opIterD-0 S W d k 0)) z≤n
opIterD-dominated S W d k (suc m) R 2≤S hk hm hR =
  ≤-trans (≤-reflexive (opIterD-suc S W d k m 0))
    (≤-trans (fIterD-lvls S W d k
                (suc (widAt S W (climb S W d k m))) (climb S W d k m) 2≤S)
             (opIterD-budget S W d k m R 2≤S hk hm hR))
