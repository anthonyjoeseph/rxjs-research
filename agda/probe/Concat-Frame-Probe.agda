------------------------------------------------------------------
-- ONE ARITHMETIC BRIDGE: a `concatAll` drain reported its walk in
-- `sIterD` currency at the INHERITED budget `k` over a queue of length
-- `m`; the enclosing FRAME must report in `fLvlD` currency at one
-- higher depth.
--
-- The composition is THREE existing lemmas, no new arithmetic:
--   1. `walk-room` (Caps-Chain.agda:521) raises the queue-length index
--      from `m ≤ widAt S W j` up to the full `suc (widAt S W j)`, and
--      that raise is exactly where the `suc j₁` in the goal comes from
--      (one spare payload slot is worth one level, `sIterD-sadd`).  This
--      ALREADY produces the goal's `suc j₁` — no separate frame receipt
--      (`fCharge`) needs to be spent for it, because `fLvlD`'s own base
--      point `fLvl S W j = j + fCharge S W j` absorbs that receipt by
--      plain inflation (step 3 below).
--   2. `sIterD-mono` (Caps.agda:680), applied twice at fixed
--      `S W d m'` — once to raise `k` up to the `suc (sizeAt S (suc
--      j))` that `fLvlD`'s `suc d` clause reads, once to raise the base
--      entry level `j` up to `fLvl S W j` (using `m≤m+n` for `j ≤ fLvl
--      S W j`, since `fLvl S W j = j + fCharge S W j`).
--   3. `fLvlD-suc` (Evaluator.agda ~795) folds the resulting `sIterD`
--      term back into `fLvlD S W (suc d) j` by definition.
--
-- So `frame-step` (Caps-Chain.agda:130) turned out NOT to be needed:
-- its `j₀`-receipt machinery is for callers that spend an EXPLICIT
-- frame charge, but here the "one slot charged for the frame" is
-- already the `suc j₁` `walk-room` produces, and the fCharge receipt is
-- absorbed for free by inflation (fCharge is never even mentioned
-- below, other than through `fLvl`'s definition).
--
-- METHOD NOTE (outside-in): the statement below was first typechecked
-- with a `{!!}` body — against exactly the imports this file ends up
-- using — before any of the arithmetic was written, to confirm the
-- statement itself was well-formed. That version is not reproduced
-- here; the body below is what replaced the hole once the composition
-- was found.
------------------------------------------------------------------

module Concat-Frame-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)

open import Rx.Evaluator
  using (sizeAt; widAt; fCharge; fLvl; fLvlD; sIterD; fLvlD-suc)
open import Verify-Budget-Sufficient.Caps
  using (sIterD-mono)
open import Verify-Budget-Sufficient.Caps-Chain
  using (walk-room)

------------------------------------------------------------------
-- § 1.  CORNER CHECKS, before grinding.
--
-- d = 0, m = 0, j = 0, k = 0, j₁ = 0 all together: S := 2, W := 0.
-- The point of this section is only that the HYPOTHESES are
-- satisfiable at the corner — i.e. that the statement is not
-- vacuously unreachable there — NOT a proof of the corner itself.
--
-- The walk premise at the corner, `0 + 0 ≤ sIterD 2 0 0 0 0 0`, is
-- `0 ≤ sIterD S W d k 0 J`, which is `0 ≤ J` by `sIterD-0`
-- (`sIterD S W d k 0 J ≡ J`) at `J := 0` — trivially true (`z≤n`
-- below). The two side hypotheses (`m ≤ widAt S W j`, `k ≤ suc
-- (sizeAt S (suc j))`) are likewise `0 ≤ _` at this corner, so also
-- trivially true. So the corner is a genuine (if degenerate) instance
-- of the statement, not a vacuous one.
------------------------------------------------------------------

corner-walk-trivial : 0 + 0 ≤ sIterD 2 0 0 0 0 0
corner-walk-trivial = z≤n

------------------------------------------------------------------
-- § 2.  THE PROOF.
------------------------------------------------------------------

-- j ≤ fLvl S W j, since fLvl S W J = J + fCharge S W J
j≤fLvl : ∀ (S W j : ℕ) → j ≤ fLvl S W j
j≤fLvl S W j = m≤m+n j (fCharge S W j)

concat-frame : ∀ (S W d k m j j₁ : ℕ) → 2 ≤ S →
  m ≤ widAt S W j →
  k ≤ suc (sizeAt S (suc j)) →
  j + j₁ ≤ sIterD S W d k m j →
  j + suc j₁ ≤ fLvlD S W (suc d) j
concat-frame S W d k m j j₁ 2≤S hm hk h =
  ≤-trans
    (≤-trans
      -- step 1: raise the queue-length index m up to suc (widAt S W j)
      -- at the SAME k — this is where the goal's `suc j₁` comes from
      (walk-room S W d k m j j₁ 2≤S hm h)
      -- step 2: raise k up to the suc (sizeAt S (suc j)) that fLvlD's
      -- suc-d clause reads, at the SAME entry level j
      (sIterD-mono (suc (widAt S W j)) (suc (widAt S W j)) d d k
         (suc (sizeAt S (suc j))) 2≤S ≤-refl ≤-refl ≤-refl ≤-refl hk ≤-refl))
    (≤-trans
      -- step 3: raise the entry level from j up to fLvl S W j (free,
      -- by inflation — this is the "one slot charged for the frame"
      -- absorbed without an explicit fCharge receipt)
      (sIterD-mono (suc (widAt S W j)) (suc (widAt S W j)) d d
         (suc (sizeAt S (suc j))) (suc (sizeAt S (suc j))) 2≤S ≤-refl ≤-refl
         (j≤fLvl S W j) ≤-refl ≤-refl ≤-refl)
      -- step 4: fold back into fLvlD S W (suc d) j by definition
      (≤-reflexive (sym (fLvlD-suc S W d j))))
