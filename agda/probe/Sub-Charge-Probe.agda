------------------------------------------------------------------
-- THE SUBSCRIBE-CHARGE PROBE: what does ONE subscribe cost, and can a
-- LEVEL-READ function bound it?
--
-- The two remaining *All frame faces (`innerFinish-concat-face`,
-- `thruOuter-face`, .Caps-Face) and .Wet's GAP (a) all wait on ONE
-- number: the growth index `subscribeE-caps` reports.  Its `j′` is an
-- unbounded existential, and `thruWalk-caps` / `concatDrain-caps`
-- produce theirs by SUMMING it.  The design ruling that sent this leg
-- named a candidate — "one subscribe walks the inner's operator chain,
-- one receipt per operator, no frame growth beyond the receipts;
-- candidate ~2·sizeAt S J".
--
-- THAT CANDIDATE IS TOO SMALL, AND NOT BY A CONSTANT.  This probe
-- reads the clause table off the ground companion tree, finds the
-- shape the receipts actually compose in, and gates the replacement.
--
------------------------------------------------------------------
-- § 0  THE CLAUSE TABLE — where `subscribeE-caps`'s j′ comes from,
--      clause by clause (.Caps-Face, the GROUND definitions).
--
--   emptyᵉ            0
--   takeᵉ, count 0    0                 (never subscribes its source)
--   μᵉ, out of gas    0                 (a dry close)
--   varᵉ              — (impossible in a closed expression)
--   deferᵉ            1                 (the registration)
--   ofᵉ ts            suc (sizeᵗˢ ts)   evalTms-caps, ≤ suc (sizeAt S J)
--   mapᵉ f b          suc (j₁ + j₂)     j₁ = the SOURCE's subscribe at
--                                       J+1, j₂ = pushBurst's
--   takeᵉ (suc k) b   suc (j₁ + j₂)     same
--   scanᵉ f z b       j₀ + suc (j₁ + j₂)  j₀ = evalSeed-caps,
--                                       ≤ suc (sizeAt S J)
--   the four *All     subscribeAll-caps = suc (j₁ + j₂), same shape
--   μᵉ, with gas      j₀ + j₁           j₀ = unfoldμ-caps (m + suc (m*m)),
--                                       j₁ = the UNFOLDING's subscribe
--   input i           subscribeE-input-caps: a scripted slot is 1, a
--                     SHARED slot is sharedSlot-caps, whose j′ is the
--                     def's own subscribe
--
-- and `pushBurst-caps`'s j₂ is `Σ` over the burst's emits of
-- `stepFrame-caps`'s j′ — ONE FRAME PER EMIT.
--
-- § 1  SO THE SUBSCRIBE CHARGE IS MUTUALLY RECURSIVE WITH THE FRAME
--      CHARGE, and that is the finding.  A subscribe of `mergeAllᵉ b`
--      installs a `thru-outer` frame and pushes b's burst back through
--      it; that frame is `thruWalk`, which subscribes ONE INNER PER
--      PAYLOAD; and that inner's subscribe runs frames of its own.  So
--
--          one frame  ⟶  ≤ suc (widAt S W J) subscribes
--          one subscribe ⟶  ≤ suc (sizeAt S J) operators,
--                           each ⟶ ≤ suc (widAt S W J) frames
--
--      and NO closed form in (S, W, J) closes that loop — the same
--      failure `dCapᶜ` already took on the delivery side ("EVERY CLOSED
--      FORM FAILS, AND NOT BY A CONSTANT", Rx.Evaluator).  The repair is
--      the same one: a RECURSION whose depth is a budget read at the
--      entry caps, with every level quantity read at the level the walk
--      has climbed to.  `k` below is that budget — the SUBSCRIBE-NESTING
--      depth — and it is what `dCapᶜ`'s `suc (cSize c)` gas is for
--      deliveries.
--
-- § 2  AND THE LOOP IS NOT GAS-ESCAPING, which had to be checked before
--      any of this was worth writing.  The obvious way to breach any
--      level-read bound is a SYNCHRONOUS fixpoint: `μ x. mergeAll (of x)`
--      would re-enter `subscribeE` once per unfolding, bounded by the
--      GAS and by nothing else — and `budgetAt` is a tower THREE STORIES
--      ABOVE `capsAt`, so no function of the Caps triple could pay for
--      it.  It is a TYPE ERROR: `μᵉ` binds into Δᵍ, `varᵉ` reads Δ, and
--      `deferᵉ : Exp Γ [] (Δᵍ ++ Δ) Θ t → Exp Γ Δᵍ Δ Θ t` is the sole
--      gate moving Δᵍ into scope (Rx.Exp) — so a μ's self-reference is
--      reachable only across a TICK.  `unfoldμ body` therefore mentions
--      `μᵉ body` only under a `deferᵉ`, and one subscribe unfolds a μ at
--      most as many times as the syntax nests them.  The μ clause's own
--      `j₀ = m + suc (m * m)` is then a per-operator cost like any
--      other, and § 3's `opIterK` pays it.
--
-- § 3  THE HIERARCHY, and it is stated as LEVELS rather than as charges
--      — `fLvl S W J = J + fCharge S W J` already is one, and a level
--      transformer composes where a charge would have to be re-added at
--      the wrong level (the Entry-Caps-Refuted error, one stratum down).
--
-- § 4  THE GATE.  `fLvl≤fLvlK`: the new per-frame level DOMINATES the
--      old one pointwise at every nesting budget, including k = 0.  So
--      every consumer above `fLvl` — `iterL`, `dLvl`, `lvls`,
--      `sizeCount`, `count-gate`, the whole Level-Walk-Probe ladder —
--      follows by the monotonicity lemmas already proven, with no
--      arithmetic re-derived and no measured row re-run.  That is the
--      property the ruling asked for in Step 2, and it is why enlarging
--      the per-frame receipt is cheap now in a way it was not a week
--      ago.
--
-- WHAT IS NOT HERE, and is the next design ruling.  `k`'s INSTANTIATION.
-- The subscribe-nesting depth is bounded by the *All-nesting of the
-- values in play, every one of which is under `valCaps?`'s size half —
-- so `suc (sizeAt S J)` is the natural reading, exactly as `cDel` reads
-- `suc (cSize c)` for the dispatch depth.  But `cDel`'s gas is read ONCE
-- AT THE ENTRY CAPS while the levels are read at the current level, and
-- the same crudeness is being inherited here rather than proven.  A
-- value emitted at level J′ > J is bounded by `sizeAt S J′`, not by
-- `sizeAt S J`, so "depth ≤ the entry size cap" is a claim about which
-- values a run can BUILD, not an inequality between two level reads.
-- It is the one statement-level thing this shape still owes.
------------------------------------------------------------------
module Sub-Charge-Probe where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------
-- the repo's arithmetic, off the walk probe that already carries it —
-- `foldStep` / `iterFold` / `sizeStep` / `iterSize` / `sizeAt` /
-- `widAt` / `fCharge` / `fLvl` and their monotonicity, all copies of
-- Rx.Evaluator's, so this probe costs no rebuild of the tree either
------------------------------------------------------------------

open import Level-Walk-Probe
  using (foldStep; iterFold; sizeStep; iterSize; sizeAt; widAt;
         fCharge; fLvl; iterL; dLvl; lvls; chargeAt;
         sizeAt-mono; widAt-mono; fCharge-mono; fLvl-mono;
         iterL-mono; lvls-mono; lvls-lin)

------------------------------------------------------------------
-- § 3  THE NESTING-INDEXED HIERARCHY.
--
-- `k` is the SUBSCRIBE-NESTING budget: how many times a frame's payload
-- may be an observable whose own subscribe runs frames.  At k = 0 the
-- floor is the old receipt and nothing else, which is what makes the
-- gate below a `≤` with no side condition.
--
-- Every level quantity is read at the level the walk HAS CLIMBED TO,
-- never at the entry — `opIterK` re-reads `widAt` and `sizeAt` at its
-- own J, and `sIterK` re-enters `sLvlK` at the level the previous
-- subscribe left.  Charging any of them once at the entry is the
-- refuted error (agda/probe/Entry-Caps-Refuted.agda) one stratum down.
------------------------------------------------------------------

mutual

  -- ONE FRAME that ran at J: its own receipt, then one inner subscribe
  -- per payload — at most `suc (widAt S W J)` of them, which is
  -- `valsCaps?`'s own length conjunct
  fLvlK : ℕ → ℕ → ℕ → ℕ → ℕ
  fLvlK S W k J = sIterK S W k (suc (widAt S W J)) (fLvl S W J)

  -- m subscribes in sequence, each at the level the one before it LEFT
  sIterK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  sIterK S W k zero    J = J
  sIterK S W k (suc m) J = sIterK S W k m (sLvlK S W k J)

  -- ONE SUBSCRIBE at J.  It walks the target's operator chain, and the
  -- chain is no longer than the size cap (`sizeᵉ b ≤ cSize`, the
  -- telescope's own hypothesis)
  sLvlK : ℕ → ℕ → ℕ → ℕ → ℕ
  sLvlK S W zero    J = J
  sLvlK S W (suc k) J = opIterK S W k (suc (sizeAt S J)) J

  -- ONE OPERATOR of that chain: one j for the frame the chain gains
  -- (frameStep-chain-suc), one EVAL receipt — `ofᵉ`'s literal list,
  -- `scanᵉ`'s seed, `μᵉ`'s unfolding, all under `suc (sizeAt S J)` by
  -- their own clauses — and then `pushBurst`: the source's burst back
  -- through that frame, ONE FRAME PER EMIT
  opIterK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  opIterK S W k zero    J = J
  opIterK S W k (suc m) J =
    opIterK S W k m (fIterK S W k (suc (widAt S W J)) (suc (J + suc (sizeAt S J))))

  fIterK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  fIterK S W k zero    J = J
  fIterK S W k (suc m) J = fIterK S W k m (fLvlK S W k J)

-- and the per-frame level the walk would read, with the budget
-- instantiated at the size cap — see the header for what this
-- instantiation still owes
fLvl′ : ℕ → ℕ → ℕ → ℕ
fLvl′ S W J = fLvlK S W (suc (sizeAt S J)) J

------------------------------------------------------------------
-- § 3a  EVERY TRANSFORMER IS INFLATIONARY.  This is the whole content
-- of the gate: a level never goes down, so the old receipt survives
-- inside the new one as its first step
------------------------------------------------------------------

mutual

  fLvlK-infl : ∀ (S W k J : ℕ) → J ≤ fLvlK S W k J
  fLvlK-infl S W k J =
    ≤-trans (m≤m+n J (fCharge S W J))
            (sIterK-infl S W k (suc (widAt S W J)) (fLvl S W J))

  sIterK-infl : ∀ (S W k m J : ℕ) → J ≤ sIterK S W k m J
  sIterK-infl S W k zero    J = ≤-refl
  sIterK-infl S W k (suc m) J =
    ≤-trans (sLvlK-infl S W k J) (sIterK-infl S W k m (sLvlK S W k J))

  sLvlK-infl : ∀ (S W k J : ℕ) → J ≤ sLvlK S W k J
  sLvlK-infl S W zero    J = ≤-refl
  sLvlK-infl S W (suc k) J = opIterK-infl S W k (suc (sizeAt S J)) J

  opIterK-infl : ∀ (S W k m J : ℕ) → J ≤ opIterK S W k m J
  opIterK-infl S W k zero    J = ≤-refl
  opIterK-infl S W k (suc m) J =
    ≤-trans (≤-trans (n≤1+n J) (s≤s (m≤m+n J (suc (sizeAt S J)))))
      (≤-trans (fIterK-infl S W k (suc (widAt S W J)) (suc (J + suc (sizeAt S J))))
               (opIterK-infl S W k m
                  (fIterK S W k (suc (widAt S W J)) (suc (J + suc (sizeAt S J))))))

  fIterK-infl : ∀ (S W k m J : ℕ) → J ≤ fIterK S W k m J
  fIterK-infl S W k zero    J = ≤-refl
  fIterK-infl S W k (suc m) J =
    ≤-trans (fLvlK-infl S W k J) (fIterK-infl S W k m (fLvlK S W k J))

------------------------------------------------------------------
-- § 3b  AND MONOTONE IN EVERY ARGUMENT, the nesting budget included.
-- This is what makes the rewiring `fLvl := fLvlK` cheap: `iterL-mono`,
-- `dLvl-mono`, `lvls-mono` and `dCapᶜ-mono` are all built from
-- `fLvl-mono` and nothing else, so the whole ladder above the frame
-- moves up with this one lemma and no re-derivation
------------------------------------------------------------------

mutual

  fLvlK-mono : ∀ {S S′ W W′ J J′} (k k′ : ℕ) → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
    k ≤ k′ → fLvlK S W k J ≤ fLvlK S′ W′ k′ J′
  fLvlK-mono {S} {S′} {W} {W′} {J} {J′} k k′ 2≤S hS hW hJ hk =
    sIterK-mono (suc (widAt S W J)) (suc (widAt S′ W′ J′)) k k′ 2≤S hS hW
      (fLvl-mono 2≤S hS hW hJ) hk (s≤s (widAt-mono 2≤S hS hW hJ))

  sIterK-mono : ∀ {S S′ W W′ J J′} (m m′ k k′ : ℕ) →
    2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → k ≤ k′ → m ≤ m′ →
    sIterK S W k m J ≤ sIterK S′ W′ k′ m′ J′
  sIterK-mono {S′ = S′} {W′ = W′} {J′ = J′} zero m′ k k′ 2≤S hS hW hJ hk hm =
    ≤-trans hJ (sIterK-infl S′ W′ k′ m′ J′)
  sIterK-mono (suc m) zero    k k′ 2≤S hS hW hJ hk ()
  sIterK-mono (suc m) (suc m′) k k′ 2≤S hS hW hJ hk (s≤s hm) =
    sIterK-mono m m′ k k′ 2≤S hS hW (sLvlK-mono k k′ 2≤S hS hW hJ hk) hk hm

  sLvlK-mono : ∀ {S S′ W W′ J J′} (k k′ : ℕ) → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
    k ≤ k′ → sLvlK S W k J ≤ sLvlK S′ W′ k′ J′
  sLvlK-mono {S′ = S′} {W′ = W′} {J′ = J′} zero k′ 2≤S hS hW hJ hk =
    ≤-trans hJ (sLvlK-infl S′ W′ k′ J′)
  sLvlK-mono (suc k) zero    2≤S hS hW hJ ()
  sLvlK-mono {S} {S′} {J = J} {J′ = J′} (suc k) (suc k′) 2≤S hS hW hJ (s≤s hk) =
    opIterK-mono (suc (sizeAt S J)) (suc (sizeAt S′ J′)) k k′ 2≤S hS hW hJ hk
      (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ))

  opIterK-mono : ∀ {S S′ W W′ J J′} (m m′ k k′ : ℕ) →
    2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → k ≤ k′ → m ≤ m′ →
    opIterK S W k m J ≤ opIterK S′ W′ k′ m′ J′
  opIterK-mono {S′ = S′} {W′ = W′} {J′ = J′} zero m′ k k′ 2≤S hS hW hJ hk hm =
    ≤-trans hJ (opIterK-infl S′ W′ k′ m′ J′)
  opIterK-mono (suc m) zero    k k′ 2≤S hS hW hJ hk ()
  opIterK-mono {S} {S′} {W} {W′} {J} {J′} (suc m) (suc m′) k k′
               2≤S hS hW hJ hk (s≤s hm) =
    opIterK-mono m m′ k k′ 2≤S hS hW
      (fIterK-mono (suc (widAt S W J)) (suc (widAt S′ W′ J′)) k k′ 2≤S hS hW
         (s≤s (+-mono-≤ hJ (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ))))
         hk (s≤s (widAt-mono 2≤S hS hW hJ)))
      hk hm

  fIterK-mono : ∀ {S S′ W W′ J J′} (m m′ k k′ : ℕ) →
    2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → k ≤ k′ → m ≤ m′ →
    fIterK S W k m J ≤ fIterK S′ W′ k′ m′ J′
  fIterK-mono {S′ = S′} {W′ = W′} {J′ = J′} zero m′ k k′ 2≤S hS hW hJ hk hm =
    ≤-trans hJ (fIterK-infl S′ W′ k′ m′ J′)
  fIterK-mono (suc m) zero    k k′ 2≤S hS hW hJ hk ()
  fIterK-mono (suc m) (suc m′) k k′ 2≤S hS hW hJ hk (s≤s hm) =
    fIterK-mono m m′ k k′ 2≤S hS hW (fLvlK-mono k k′ 2≤S hS hW hJ hk) hk hm

-- and the budget's own instantiation is monotone too, since `sizeAt`
-- is: the per-frame level with the budget read off the size cap
fLvl′-mono : ∀ {S S′ W W′ J J′} → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
  fLvl′ S W J ≤ fLvl′ S′ W′ J′
fLvl′-mono {S} {S′} {J = J} {J′ = J′} 2≤S hS hW hJ =
  fLvlK-mono (suc (sizeAt S J)) (suc (sizeAt S′ J′)) 2≤S hS hW hJ
    (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ))

------------------------------------------------------------------
-- § 4  THE GATE.  The new per-frame level dominates the old one
-- POINTWISE, at EVERY nesting budget — the old receipt is literally the
-- seed of the new iteration, so this needs no arithmetic at all.
--
-- That is the whole Step-2 requirement: everything above `fLvl` in the
-- walk (`iterL`, `dLvl`, `lvls`, `sizeCount`, and the count gate) is
-- built out of `fLvl` by monotone combinators already proven
-- (Level-Walk-Probe § B/§ C), so a bigger `fLvl` moves every one of
-- them up and no measured row is re-run
------------------------------------------------------------------

fLvl≤fLvlK : ∀ (S W k J : ℕ) → fLvl S W J ≤ fLvlK S W k J
fLvl≤fLvlK S W k J = sIterK-infl S W k (suc (widAt S W J)) (fLvl S W J)

fLvl≤fLvl′ : ∀ (S W J : ℕ) → fLvl S W J ≤ fLvl′ S W J
fLvl≤fLvl′ S W J = fLvl≤fLvlK S W (suc (sizeAt S J)) J

-- and the floor is EXACTLY the old receipt: at k = 0 no payload's
-- subscribe is charged anything, so the two agree by refl.  This is
-- what makes the hierarchy a strict generalisation rather than a
-- replacement — the same relation `foldStep` has to the `2 ^ suc w` it
-- replaced
fLvlK-0 : ∀ (S W J : ℕ) → fLvlK S W 0 J ≡ fLvl S W J
fLvlK-0 S W J = go (suc (widAt S W J)) (fLvl S W J)
  where
  go : ∀ (m J′ : ℕ) → sIterK S W 0 m J′ ≡ J′
  go zero    J′ = refl
  go (suc m) J′ = go m J′

------------------------------------------------------------------
-- § 5  THE TWO FACES' ARITHMETIC, now that the shape exists.
--
-- `thruOuter-face` is one `thruWalk`: one `thruConsume` per payload,
-- each of which SUBSCRIBES an inner and appends `splitBurst`'s values.
-- Its two conjuncts are
--
--   (a) THE RECEIPT.  `Σ over the payloads of one subscribe's j′`,
--       charged against the per-frame level.  With the hierarchy that
--       is `sIterK`'s own body: `fLvlK` iterates `sLvlK` exactly
--       `suc (widAt S W J)` times starting from `fLvl S W J`, and
--       `valsCaps?`'s length conjunct is what bounds the payload count
--       by `suc (Caps.cWid (frameStep J c))` = `suc (widAt S W J)`.
--       So the face's conclusion `j + j′ ≤ fLvlK S W k j` is
--       DEFINITIONALLY the walk it performs, which is the point of
--       stating the charge as a level transformer.
--
--   (b) THE COUNT, and it is the affordable half (Worker 33's reading,
--       re-checked here): each payload's own burst contributes at most
--       `suc (cWid)` values, there are at most `suc (cWid)` payloads,
--       so the appended list is at most `suc cWid * suc cWid` long —
--       and ONE level takes cWid to `S ^ suc cWid` (frameStep-wid-suc),
--       which dominates a square as soon as `2 ≤ S`.  The inequality is
--       `suc W * suc W ≤ suc (foldStep S W)`, i.e. `n² ≤ 2ⁿ + 1` at
--       `n = suc W`, TIGHT at n = 3 (9 against 9) and slack either side
--       — it is named here rather than proven because it belongs beside
--       `frameStep-wid-suc` in .Caps, not in a probe, and because § 5(a)
--       is the conjunct that decides whether the shape is right
------------------------------------------------------------------

-- the (b) gate, at the tight rung and its neighbours: the square of the
-- entry width against ONE fold of it, at S = 2 (the smallest cSize the
-- face admits, so the worst case)
_ : (suc 2 * suc 2 ≤ᵇ suc (foldStep 2 2)) ≡ true
_ = refl

_ : (suc 3 * suc 3 ≤ᵇ suc (foldStep 2 3)) ≡ true
_ = refl

_ : (suc 6 * suc 6 ≤ᵇ suc (foldStep 2 6)) ≡ true
_ = refl
