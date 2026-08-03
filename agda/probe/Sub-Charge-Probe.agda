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
--      The family below MIRRORS Rx.Evaluator's landed one (which is
--      `abstract` there, for the normalisation reason written at it);
--      here it is transparent so the properties can be proven at all.
--
-- § 4  THE GATE.  `fLvl≤fLvlK`: the new per-frame level DOMINATES the
--      old one pointwise at every nesting budget, including k = 0.  So
--      every consumer above `fLvl` — `iterL`, `dLvl`, `lvls`,
--      `sizeCount`, `count-gate`, the whole Level-Walk-Probe ladder —
--      follows by the monotonicity lemmas already proven, with no
--      arithmetic re-derived and no measured row re-run.
--
-- § 5  THE COMPOSITION GATE, and it is what the first draft of this
--      probe got WRONG.  A shape that terminates and is monotone is not
--      yet a shape the CLAUSES fit in: the receipts compose as a chain
--      of inflationary maps, and two of them applied in the wrong order
--      bound nothing at all.  Read off the ground clauses, three things
--      the first draft missed:
--
--        (i)   ORDER.  map / take / *All spend one j on the frame the
--              chain gains, then subscribe the SOURCE — the rest of the
--              operator chain — and only THEN push the source's burst
--              back through that frame.  The first draft ran the frames
--              first and the chain after, and no monotonicity turns one
--              order into the other.
--        (ii)  THE PAYLOAD'S OWN FRAME.  `subscribeInner` adds a
--              from-inner frame BEFORE it subscribes, so a payload costs
--              a subscribe at `suc J`, not at J.
--        (iii) THE EVAL RECEIPT IS QUADRATIC.  `unfoldμ-caps` pays
--              `m + suc (m * m)` with m ≤ the size cap; `suc B` does not
--              cover that and `suc B * suc B` does.
--
--      With those three repaired, EVERY CLAUSE SHAPE LANDS IN ONE
--      MONOTONICITY STEP — `walk-step` (a payload of thruWalk /
--      concatDrain), `op-step` (map / take / the four *All), and
--      `op-step-eval` / `op-step-mu` (the two clauses that evaluate
--      before they subscribe).  Those four are the arithmetic the step-2
--      grind consumes, proven here against the receipts as abstract
--      numbers under exactly the bound each sub-companion reports.
--
-- WHAT IS NOT HERE.  `k`'s INSTANTIATION is now ruled (the design
-- session, 2026-08-03): the budget is `suc (sizeAt S J)` READ AT EACH
-- DELIVERY'S OWN LEVEL, on three facts — the recursion descends the
-- pushed VALUE structurally within one delivery, a delivery's arriving
-- value has nesting ≤ size ≤ `sizeAt S J` by valCaps? at that level, and
-- values grown by folds are delivered LATER at a higher J.  The
-- `nestᵛ ≤ sizeᵛ` half of that is a structural lemma the step-2 pass
-- states beside the other value measures; it is not arithmetic and so
-- is not here.
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
-- may be an observable whose own subscribe runs frames.
--
-- Every level quantity is read at the level the walk HAS CLIMBED TO,
-- never at the entry — `opIterK` re-reads `widAt` at the level the
-- operator chain LEFT, and `sIterK` re-enters `sLvlK` at the level the
-- previous payload left.  Charging any of them once at the entry is the
-- refuted error (agda/probe/Entry-Caps-Refuted.agda) one stratum down.
------------------------------------------------------------------

mutual

  -- ONE FRAME that ran at J: its own receipt, then one inner subscribe
  -- per payload — at most `suc (widAt S W J)` of them, which is
  -- `valsCaps?`'s own length conjunct
  fLvlK : ℕ → ℕ → ℕ → ℕ → ℕ
  fLvlK S W k J = sIterK S W k (suc (widAt S W J)) (fLvl S W J)

  -- m payloads in sequence, each at the level the one before it LEFT.
  -- ONE PAYLOAD costs the from-inner frame its chain gains (the `suc J`
  -- — § 5 (ii)) and then the inner's subscribe at the level that frame
  -- left
  sIterK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  sIterK S W k zero    J = J
  sIterK S W k (suc m) J = sIterK S W k m (sLvlK S W k (suc J))

  -- ONE SUBSCRIBE at J.  It walks the target's operator chain, and the
  -- chain is no longer than the size cap (`sizeᵉ b ≤ cSize`, the
  -- telescope's own hypothesis)
  sLvlK : ℕ → ℕ → ℕ → ℕ → ℕ
  sLvlK S W zero    J = J
  sLvlK S W (suc k) J = opIterK S W k (suc (sizeAt S J)) J

  -- ONE OPERATOR, IN THE ORDER THE CLAUSE RUNS IT (§ 5 (i)): the frame
  -- the chain gains and the operator's own EVAL receipt (quadratic, §
  -- 5 (iii)), then a μ's re-entry at one less nesting, then the REST of
  -- the chain, and only then `pushBurst` — one frame per emit, at the
  -- level the chain left
  opIterK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  opIterK S W k zero    J = J
  opIterK S W k (suc m) J =
    let J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
        J₂ = opIterK S W k m (sLvlK S W k J₀)
    in fIterK S W k (suc (widAt S W J₂)) J₂

  fIterK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  fIterK S W k zero    J = J
  fIterK S W k (suc m) J = fIterK S W k m (fLvlK S W k J)

-- and the per-frame level the walk reads, with the budget instantiated
-- at the size cap READ AT THE FRAME'S OWN LEVEL (the ruling)
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
    ≤-trans (≤-trans (n≤1+n J) (sLvlK-infl S W k (suc J)))
            (sIterK-infl S W k m (sLvlK S W k (suc J)))

  sLvlK-infl : ∀ (S W k J : ℕ) → J ≤ sLvlK S W k J
  sLvlK-infl S W zero    J = ≤-refl
  sLvlK-infl S W (suc k) J = opIterK-infl S W k (suc (sizeAt S J)) J

  opIterK-infl : ∀ (S W k m J : ℕ) → J ≤ opIterK S W k m J
  opIterK-infl S W k zero    J = ≤-refl
  opIterK-infl S W k (suc m) J =
    ≤-trans (≤-trans (≤-trans (n≤1+n J)
                              (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J)))))
                     (≤-trans (sLvlK-infl S W k
                                 (suc (J + suc (sizeAt S J) * suc (sizeAt S J))))
                              (opIterK-infl S W k m
                                 (sLvlK S W k
                                    (suc (J + suc (sizeAt S J) * suc (sizeAt S J)))))))
            (fIterK-infl S W k
               (suc (widAt S W (opIterK S W k m
                       (sLvlK S W k
                          (suc (J + suc (sizeAt S J) * suc (sizeAt S J)))))))
               (opIterK S W k m
                  (sLvlK S W k (suc (J + suc (sizeAt S J) * suc (sizeAt S J))))))

  fIterK-infl : ∀ (S W k m J : ℕ) → J ≤ fIterK S W k m J
  fIterK-infl S W k zero    J = ≤-refl
  fIterK-infl S W k (suc m) J =
    ≤-trans (fLvlK-infl S W k J) (fIterK-infl S W k m (fLvlK S W k J))

------------------------------------------------------------------
-- § 3b  AND MONOTONE IN EVERY ARGUMENT, the nesting budget included.
-- This is what makes the rewiring `fLvl := fLvl′` cheap: `iterL-mono`,
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
    sIterK-mono m m′ k k′ 2≤S hS hW (sLvlK-mono k k′ 2≤S hS hW (s≤s hJ) hk) hk hm

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
    fIterK-mono (suc (widAt S W X)) (suc (widAt S′ W′ X′)) k k′ 2≤S hS hW
      inner hk (s≤s (widAt-mono 2≤S hS hW inner))
    where
    sz≤ = sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ
    J₀≤ : suc (J + suc (sizeAt S J) * suc (sizeAt S J))
            ≤ suc (J′ + suc (sizeAt S′ J′) * suc (sizeAt S′ J′))
    J₀≤ = s≤s (+-mono-≤ hJ (*-mono-≤ (s≤s sz≤) (s≤s sz≤)))
    X  = opIterK S W k m
           (sLvlK S W k (suc (J + suc (sizeAt S J) * suc (sizeAt S J))))
    X′ = opIterK S′ W′ k′ m′
           (sLvlK S′ W′ k′ (suc (J′ + suc (sizeAt S′ J′) * suc (sizeAt S′ J′))))
    inner : X ≤ X′
    inner = opIterK-mono m m′ k k′ 2≤S hS hW (sLvlK-mono k k′ 2≤S hS hW J₀≤ hk) hk hm

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

------------------------------------------------------------------
-- § 5  THE COMPOSITION GATE — one lemma per clause SHAPE of the ground
-- tree.  Each takes the receipts as abstract numbers under exactly the
-- bound its own sub-companion reports, and lands the clause's total
-- inside the transformer.  These are the arithmetic steps the step-2
-- grind consumes; the shape is right precisely because they go through
-- with the pieces the clauses already hand back, and the first draft's
-- shape admitted none of them.
------------------------------------------------------------------

-- ONE PAYLOAD of a thruWalk / concatDrain: the head subscribes an inner
-- under one more frame (`subscribeInner-caps` recurses at `suc j`), and
-- the tail is the walk's own IH at the level the head left
walk-step : ∀ (S W k m j j₁ j₂ : ℕ) → 2 ≤ S →
  j + j₁ ≤ sLvlK S W k (suc j) →
  (j + j₁) + j₂ ≤ sIterK S W k m (j + j₁) →
  j + (j₁ + j₂) ≤ sIterK S W k (suc m) j
walk-step S W k m j j₁ j₂ 2≤S hd tl =
  ≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₁ j₂))) tl)
          (sIterK-mono m m k k 2≤S ≤-refl ≤-refl hd ≤-refl ≤-refl)

-- ONE OPERATOR, map / take / *All shape: one j for the frame the chain
-- gains, the SOURCE's subscribe at `suc j`, then pushBurst's frames at
-- the level that subscribe left
op-step : ∀ (S W k m j j₁ j₂ : ℕ) → 2 ≤ S →
  suc j + j₁ ≤ opIterK S W k m (suc j) →
  (suc j + j₁) + j₂ ≤ fIterK S W k (suc (widAt S W (suc j + j₁))) (suc j + j₁) →
  j + suc (j₁ + j₂) ≤ opIterK S W k (suc m) j
op-step S W k m j j₁ j₂ 2≤S src pb =
  ≤-trans (≤-trans (≤-reflexive (trans (+-suc j (j₁ + j₂))
                                       (cong suc (sym (+-assoc j j₁ j₂)))))
                   pb)
          (fIterK-mono (suc (widAt S W (suc j + j₁))) (suc (widAt S W X)) k k
             2≤S ≤-refl ≤-refl A≤X ≤-refl (s≤s (widAt-mono 2≤S ≤-refl ≤-refl A≤X)))
  where
  J₀ = suc (j + suc (sizeAt S j) * suc (sizeAt S j))
  X  = opIterK S W k m (sLvlK S W k J₀)
  sucj≤J₁ : suc j ≤ sLvlK S W k J₀
  sucj≤J₁ = ≤-trans (s≤s (m≤m+n j (suc (sizeAt S j) * suc (sizeAt S j))))
                    (sLvlK-infl S W k J₀)
  A≤X : suc j + j₁ ≤ X
  A≤X = ≤-trans src (opIterK-mono m m k k 2≤S ≤-refl ≤-refl sucj≤J₁ ≤-refl ≤-refl)

-- ONE OPERATOR, scan shape: an EVAL receipt first (`evalSeed-caps`,
-- `suc (sizeᵗ z)`, so at most `suc (sizeAt S j)`), then the same three
op-step-eval : ∀ (S W k m j j₀ j₁ j₂ : ℕ) → 2 ≤ S →
  j₀ ≤ suc (sizeAt S j) →
  suc (j + j₀) + j₁ ≤ opIterK S W k m (suc (j + j₀)) →
  (suc (j + j₀) + j₁) + j₂
    ≤ fIterK S W k (suc (widAt S W (suc (j + j₀) + j₁))) (suc (j + j₀) + j₁) →
  j + (j₀ + suc (j₁ + j₂)) ≤ opIterK S W k (suc m) j
op-step-eval S W k m j j₀ j₁ j₂ 2≤S hj₀ src pb =
  ≤-trans (≤-trans (≤-reflexive (trans (sym (+-assoc j j₀ (suc (j₁ + j₂))))
                                  (trans (+-suc (j + j₀) (j₁ + j₂))
                                         (cong suc (sym (+-assoc (j + j₀) j₁ j₂))))))
                   pb)
          (fIterK-mono (suc (widAt S W (suc (j + j₀) + j₁))) (suc (widAt S W X)) k k
             2≤S ≤-refl ≤-refl A≤X ≤-refl (s≤s (widAt-mono 2≤S ≤-refl ≤-refl A≤X)))
  where
  J₀ = suc (j + suc (sizeAt S j) * suc (sizeAt S j))
  X  = opIterK S W k m (sLvlK S W k J₀)
  seed≤ : suc (j + j₀) ≤ sLvlK S W k J₀
  seed≤ = ≤-trans (s≤s (+-monoʳ-≤ j
                    (≤-trans hj₀ (m≤m*n (suc (sizeAt S j)) (suc (sizeAt S j))))))
                  (sLvlK-infl S W k J₀)
  A≤X : suc (j + j₀) + j₁ ≤ X
  A≤X = ≤-trans src (opIterK-mono m m k k 2≤S ≤-refl ≤-refl seed≤ ≤-refl ≤-refl)

-- B + suc (B · B) ≤ suc B · suc B — the arithmetic the μ receipt needs,
-- and the reason the per-operator eval receipt is a SQUARE
quad-arith : ∀ (B : ℕ) → B + suc (B * B) ≤ suc B * suc B
quad-arith B =
  ≤-trans (≤-reflexive (+-suc B (B * B)))
          (≤-trans (s≤s (+-monoʳ-≤ B (m≤n+m (B * B) B)))
                   (≤-reflexive (sym (cong (λ x → suc (B + x)) (*-suc B B)))))

-- THE μ OPERATOR: the unfolding receipt `m₀ + suc (m₀ * m₀)`, and then a
-- FRESH subscribe on a LARGER term — which is why it is charged as one
-- NESTING level rather than as a continuation of the same chain, and
-- why the budget k has to count μ-nesting as well as *All-nesting
op-step-mu : ∀ (S W k m j m₀ j₁ : ℕ) → 2 ≤ S →
  m₀ ≤ sizeAt S j →
  (j + (m₀ + suc (m₀ * m₀))) + j₁ ≤ sLvlK S W k (j + (m₀ + suc (m₀ * m₀))) →
  j + ((m₀ + suc (m₀ * m₀)) + j₁) ≤ opIterK S W k (suc m) j
op-step-mu S W k m j m₀ j₁ 2≤S hm₀ sub =
  ≤-trans (≤-trans (≤-reflexive (sym (+-assoc j (m₀ + suc (m₀ * m₀)) j₁))) sub)
          (≤-trans (sLvlK-mono k k 2≤S ≤-refl ≤-refl quad ≤-refl)
                   (≤-trans (opIterK-infl S W k m (sLvlK S W k J₀))
                            (fIterK-infl S W k (suc (widAt S W X)) X)))
  where
  B  = sizeAt S j
  J₀ = suc (j + suc B * suc B)
  X  = opIterK S W k m (sLvlK S W k J₀)
  quad : j + (m₀ + suc (m₀ * m₀)) ≤ J₀
  quad = ≤-trans (+-monoʳ-≤ j (≤-trans (+-mono-≤ hm₀ (s≤s (*-mono-≤ hm₀ hm₀)))
                                       (quad-arith B)))
                 (n≤1+n (j + suc B * suc B))

------------------------------------------------------------------
-- § 6  THE (b) CONJUNCT of the two faces, at the tight rung and its
-- neighbours: the square of the entry width against ONE fold of it, at
-- S = 2 (the smallest cSize the face admits, so the worst case).  Each
-- payload's burst contributes at most `suc cWid` values and there are
-- at most `suc cWid` payloads, so the appended list is at most
-- `suc cWid * suc cWid` long — and ONE level takes cWid to
-- `S ^ suc cWid` (frameStep-wid-suc), which dominates a square as soon
-- as `2 ≤ S`.  TIGHT at n = 3 (9 against 9) and slack either side
------------------------------------------------------------------

_ : (suc 2 * suc 2 ≤ᵇ suc (foldStep 2 2)) ≡ true
_ = refl

_ : (suc 3 * suc 3 ≤ᵇ suc (foldStep 2 3)) ≡ true
_ = refl

_ : (suc 6 * suc 6 ≤ᵇ suc (foldStep 2 6)) ≡ true
_ = refl
