-- ══════════════════════════════════════════════════════════════════
-- AND NO ADVANCE RULE IS THE REPAIR: every reading of the size walk's
-- level between a JOIN and a SUM is unaffordable at the second
-- crossing frame, at every cap this development admits.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
-- ══════════════════════════════════════════════════════════════════

-- WHAT THE STATEMENT SAYS.  A ceiling and a ledger are both closed
-- forms in the cap, the width and the level, and the evaluator's own
-- charge header records that no closed form in those three closes the
-- loop a crossing frame opens.  What answers that shape one stratum up
-- is a RECURSION ON A DEPTH FUEL with every quantity read at the level
-- the walk has CLIMBED to, so this row writes the size walk's ceiling
-- in that shape -- fuel outside, rungs threaded, the charge at each
-- rung read at the level that rung stands at -- and then quantifies
-- over the one thing left free in it: HOW the rung count advances when
-- a frame's charge arrives.

-- THE BRACKET IS THE WHOLE MECHANISM SPACE, and that is what makes
-- this a finding about the walked side rather than about one reading.
-- An advance may not fall below the count in hand, which is monotone,
-- nor below the charge, which is owed; and it need never exceed their
-- sum.  So every rule sits between a JOIN and a SUM, and both endpoints
-- are exhibited here rather than assumed -- the sum being the reading
-- the walk carries and the join the one the live face's outer arm is
-- proven in, whose receipts combine by max and do not stack.

-- WHERE IT BREAKS.  The walk factor affords a rung count POLYNOMIAL in
-- the cap: a cap squared plus a cap plus a cap squared, each spent at
-- one frame charge.  Every rule in the bracket passes that at its
-- SECOND crossing frame, and by the whole ladder rather than by a
-- factor: THREE rungs of the size ladder hold more layers than the
-- entire polynomial the factor allows, and the second frame already
-- stands three rungs up under every rule in the bracket.  The join
-- endpoint gains nothing over the sum because the two quantities it
-- chooses between are of the SAME ORDER -- a frame's charge is read at
-- the level its rung stands at -- so what a max discards is the
-- lower-order term.

-- AND THE CHARGE IS THE SMALLEST HONEST ONE, which is what makes this
-- a finding about the SHAPE rather than about a generous reading.  A
-- crossing frame charges what it subscribes, and what this climb hands
-- it is the DEEPEST MAP CHAIN the level admits and nothing else: no
-- telescope, no burst, no unfolding.  A chain spends two nodes of
-- syntax per layer over a singleton source, so a level of `B` carries
-- `⌊ B /2⌋ ∸ 1` of them -- the figure `Refuted.Walk-Ceil-Ledger` reads
-- off its own witness, which is where such an arrival is exhibited as
-- one a walk can reach rather than assumed.

-- SO THE CHANNEL IS THE LAYER TERM, AND NO DENOMINATION OF THE
-- UNFOLDING BLOCK REACHES IT.  A descent charge is a block of rungs
-- bought against the `μ` nesting plus one rung per operator, and only
-- the first half reads the bound it is charged at; the chain here
-- carries no `μ` at all, so its whole charge is operators.  Re-pricing
-- the block therefore moves this row by nothing.  What puts a frame's
-- charge at the order of the level is the layers a level's worth of
-- syntax can hold, and that is fixed by the size ladder rather than by
-- what an unfolding costs.

-- WHAT THIS DOES NOT SHOW.  It does not refute the depth-fuel shape
-- itself, which is discharged one face over and is what prices the
-- caps ladder.  What it refutes is that shape spent against THIS
-- factor: the caps face's own ceiling is defined by READING its climb,
-- so the climb is affordable there by construction, while this rung
-- count must fit under a nesting budget that is a fixed exponential in
-- a polynomial and reads nothing.  Nor does it reach a rule advancing
-- by LESS than the charge -- but such a rule does not pay a frame's
-- debt, so what it prices is not this walk.

module Refuted.Size-Climb-Afford where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _*_; _∸_; _⊔_; ⌊_/2⌋;
  s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; 1+n≰n;
  +-comm; +-mono-≤; +-monoʳ-≤; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤;
  *-identityˡ; *-identityʳ; m≤m+n; m≤n+m; m≤m⊔n; m≤n⊔m; ⊔-lub;
  m∸n≤m; ∸-monoˡ-≤; m+n≤o⇒m≤o∸n; ⌊n/2⌋-mono; ⌊n/2⌋≤n; n≡⌊n+n/2⌋)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Rx.Evaluator using (iterSize)
open import Verify-Budget-Sufficient.Caps using (iterSize-mono-count)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (frameCh)

----------------------------------------------------------------------
-- THE CEILING IN THE SHAPE THAT ANSWERS A CLOSED FORM -- fuel on the
-- outside, rungs threaded through, and the charge at each frame read
-- at the level that frame stands at rather than at the level the walk
-- entered.  It is the size walk's own reading: a frame's arrival is
-- bounded in SIZE by the level in hand, which is `iterSize S k S` at
-- rung `k`, and what the frame is charged for it is its LAYERS.
----------------------------------------------------------------------
szCh : ℕ → ℕ → ℕ                     -- cap, rungs climbed so far
szCh S k = ⌊ iterSize S k S /2⌋ ∸ 1

----------------------------------------------------------------------
-- AND THE ADVANCE LEFT FREE.  A rule takes the level in hand and the
-- charge that arrived; it may not fall below either, and it need not
-- exceed their sum.
----------------------------------------------------------------------
AdvRule : Set
AdvRule = ℕ → ℕ → ℕ

JoinToSum : AdvRule → Set
JoinToSum adv = ∀ (k c : ℕ) →
  (k ≤ adv k c) × ((c ≤ adv k c) × (adv k c ≤ k + c))

-- LOAD-BEARING: the bracket is inhabited at both ends, so the family
-- below is not a claim about rules that do not exist.  The sum is what
-- the walk carries; the join is what the live face's outer arm is
-- stated in.
sum-in-bracket : JoinToSum _+_
sum-in-bracket k c = m≤m+n k c , (m≤n+m c k , ≤-refl)

join-in-bracket : JoinToSum _⊔_
join-in-bracket k c =
  m≤m⊔n k c , (m≤n⊔m k c , ⊔-lub (m≤m+n k c) (m≤n+m c k))

advClimb : AdvRule → ℕ → ℕ → ℕ → ℕ   -- rule, cap, depth fuel, rungs
advClimb adv S zero    k = k
advClimb adv S (suc d) k = advClimb adv S d (adv k (szCh S k))

----------------------------------------------------------------------
-- WHAT THE WALK FACTOR AFFORDS, in the factor's own two pieces: the
-- ledger range its premise admits, times the per-frame charge every
-- rung of that ledger is spent at.
----------------------------------------------------------------------
walkAfford : ℕ → ℕ
walkAfford S = (S * S + S + S * S) * frameCh S S

AdvClimbAfford : Set
AdvClimbAfford = ∀ (adv : AdvRule) → JoinToSum adv →
  ∀ (S : ℕ) → 8 ≤ S → advClimb adv S 2 0 ≤ walkAfford S

module _ (adv : AdvRule) (jts : JoinToSum adv) (S : ℕ) (8≤S : 8 ≤ S) where

  1≤cap : 1 ≤ S
  1≤cap = ≤-trans (s≤s z≤n) 8≤S

  4≤cap : 4 ≤ S
  4≤cap = ≤-trans (s≤s (s≤s (s≤s (s≤s z≤n)))) 8≤S

  -- THE LEVEL AFTER ONE CROSSING FRAME, whatever the rule: the bracket
  -- pins it from both sides, since the level in hand is zero there.
  lvl₁ : ℕ
  lvl₁ = adv 0 (szCh S 0)

  chg₀≤lvl₁ : szCh S 0 ≤ lvl₁
  chg₀≤lvl₁ = proj₁ (proj₂ (jts 0 (szCh S 0)))

  lvl₁≤chg₀ : lvl₁ ≤ szCh S 0
  lvl₁≤chg₀ = proj₂ (proj₂ (jts 0 (szCh S 0)))

  -- AND IT STANDS AT LEAST THREE RUNGS UP, which is the whole of what
  -- the row below spends: the smallest cap the premise admits already
  -- holds three layers at the level a walk ENTERS at.
  3≤lvl₁ : 3 ≤ lvl₁
  3≤lvl₁ = ≤-trans (∸-monoˡ-≤ 1 (⌊n/2⌋-mono 8≤S)) chg₀≤lvl₁

  -- LOAD-BEARING: the whole ledger the factor affords sits below the
  -- LAYERS three rungs of the size ladder hold, and three rungs are
  -- what the second crossing frame's own entry level has already
  -- passed -- under every rule in the bracket, since each keeps at
  -- least the charge.
  climb-outruns-afford : suc (walkAfford S) ≤ advClimb adv S 2 0
  climb-outruns-afford = ≤-trans suc≤half (≤-trans half3≤halfLvl charge≤adv)
    where
    E2 E3 E4 : ℕ
    E2 = S * S
    E3 = S * E2
    E4 = S * E3
    1≤E2 : 1 ≤ E2
    1≤E2 = ≤-trans (≤-reflexive (sym (*-identityˡ 1))) (*-mono-≤ 1≤cap 1≤cap)
    1≤E3 : 1 ≤ E3
    1≤E3 = ≤-trans (≤-reflexive (sym (*-identityˡ 1))) (*-mono-≤ 1≤cap 1≤E2)
    E2≤E3 : E2 ≤ E3
    E2≤E3 = ≤-trans (≤-reflexive (sym (*-identityˡ E2))) (*-monoˡ-≤ E2 1≤cap)
    4E3≤E4 : 4 * E3 ≤ E4
    4E3≤E4 = *-monoˡ-≤ E3 4≤cap
    4≤E4 : 4 ≤ E4
    4≤E4 =
      ≤-trans 4≤cap
              (≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-monoʳ-≤ S 1≤E3))
    -- the factor's premise, multiplied out against its frame charge
    afford-shape : walkAfford S ≡ 2 * E4 + (3 * E3 + E2)
    afford-shape =
      solve 1 (λ a → (a :* a :+ a :+ a :* a) :* (a :* (con 1 :+ a))
                     := con 2 :* (a :* (a :* (a :* a)))
                        :+ (con 3 :* (a :* (a :* a)) :+ a :* a))
            refl S
    eq4 : 3 * E3 + E3 ≡ 4 * E3
    eq4 = solve 1 (λ b → con 3 :* b :+ b := con 4 :* b) refl E3
    eq3 : 2 * E4 + E4 ≡ 3 * E4
    eq3 = solve 1 (λ b → con 2 :* b :+ b := con 3 :* b) refl E4
    afford≤3 : walkAfford S ≤ 3 * E4
    afford≤3 =
      ≤-trans (≤-reflexive afford-shape)
              (≤-trans (+-monoʳ-≤ (2 * E4)
                          (≤-trans (+-monoʳ-≤ (3 * E3) E2≤E3)
                                   (≤-trans (≤-reflexive eq4) 4E3≤E4)))
                       (≤-reflexive eq3))
    eq8 : 6 * E4 + 2 * E4 ≡ 8 * E4
    eq8 = solve 1 (λ b → con 6 :* b :+ con 2 :* b := con 8 :* b) refl E4
    4≤2E4 : 4 ≤ 2 * E4
    4≤2E4 = ≤-trans 4≤E4 (m≤m+n E4 (E4 + 0))
    eq6+4 : (2 + 3 * E4) + (2 + 3 * E4) ≡ 6 * E4 + 4
    eq6+4 = solve 1 (λ b → (con 2 :+ con 3 :* b) :+ (con 2 :+ con 3 :* b)
                        := con 6 :* b :+ con 4) refl E4
    -- three rungs of the ladder, multiplied out
    iter3-shape : iterSize S 3 S ≡ (S + 2 * E2 + 4 * E3) + 8 * E4
    iter3-shape =
      solve 1 (λ a → a :* (con 1 :+ con 2
                            :* (a :* (con 1 :+ con 2
                                  :* (a :* (con 1 :+ con 2 :* a)))))
                     := (a :+ con 2 :* (a :* a) :+ con 4 :* (a :* (a :* a)))
                        :+ con 8 :* (a :* (a :* (a :* a))))
            refl S
    8E4≤iter3 : 8 * E4 ≤ iterSize S 3 S
    8E4≤iter3 =
      ≤-trans (m≤n+m (8 * E4) (S + 2 * E2 + 4 * E3))
              (≤-reflexive (sym iter3-shape))
    -- HALF THE LADDER IS WHAT A CHAIN CARRIES, and it is still the
    -- whole ledger and two frames over: the factor's polynomial
    -- doubled sits under three rungs outright.
    half-goal : (2 + walkAfford S) + (2 + walkAfford S) ≤ iterSize S 3 S
    half-goal =
      ≤-trans (+-mono-≤ (+-monoʳ-≤ 2 afford≤3) (+-monoʳ-≤ 2 afford≤3))
              (≤-trans (≤-reflexive eq6+4)
                       (≤-trans (+-monoʳ-≤ (6 * E4) 4≤2E4)
                                (≤-trans (≤-reflexive eq8) 8E4≤iter3)))
    half-lb : ∀ m n → m + m ≤ n → m ≤ ⌊ n /2⌋
    half-lb m n le = ≤-trans (≤-reflexive (n≡⌊n+n/2⌋ m)) (⌊n/2⌋-mono le)
    suc≤half : suc (walkAfford S) ≤ szCh S 3
    suc≤half =
      m+n≤o⇒m≤o∸n (suc (walkAfford S))
        (≤-trans (≤-reflexive (cong suc (+-comm (walkAfford S) 1)))
                 (half-lb (2 + walkAfford S) (iterSize S 3 S) half-goal))
    -- and the second frame stands no lower than three rungs
    half3≤halfLvl : szCh S 3 ≤ szCh S lvl₁
    half3≤halfLvl =
      ∸-monoˡ-≤ 1 (⌊n/2⌋-mono (iterSize-mono-count S S 1≤cap 3≤lvl₁))
    -- whatever the rule does with them, it keeps the charge
    charge≤adv : szCh S lvl₁ ≤ adv lvl₁ (szCh S lvl₁)
    charge≤adv = proj₁ (proj₂ (jts lvl₁ (szCh S lvl₁)))

  -- LOAD-BEARING, AND THE OTHER DIRECTION: one crossing frame IS
  -- affordable under every rule in the bracket, so what the row above
  -- reports is the second frame and not an arithmetic that was never
  -- satisfiable.
  one-frame-affordable : advClimb adv S 1 0 ≤ walkAfford S
  one-frame-affordable =
    ≤-trans lvl₁≤chg₀
            (≤-trans (≤-trans (m∸n≤m ⌊ S /2⌋ 1) (⌊n/2⌋≤n S))
                     (≤-trans (≤-reflexive (sym (*-identityʳ S)))
                              (*-mono-≤ ledger 1≤frame)))
    where
    ledger : S ≤ S * S + S + S * S
    ledger = ≤-trans (m≤n+m S (S * S)) (m≤m+n (S * S + S) (S * S))
    1≤frame : 1 ≤ frameCh S S
    1≤frame =
      ≤-trans (≤-reflexive (sym (*-identityˡ 1))) (*-mono-≤ 1≤cap (s≤s z≤n))

adv-climb-afford-absurd : AdvClimbAfford → ⊥
adv-climb-afford-absurd pr = go _+_ sum-in-bracket 8 ≤-refl
  where
  go : ∀ (adv : AdvRule) → JoinToSum adv → ∀ (S : ℕ) → 8 ≤ S → ⊥
  go adv jts S h =
    1+n≰n (≤-trans (climb-outruns-afford adv jts S h) (pr adv jts S h))
