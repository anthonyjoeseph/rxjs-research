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
--      the same one: a RECURSION whose every level quantity is read at
--      the level the walk has CLIMBED TO, re-read at each frame entry.
--      `k` is that budget — the SUBSCRIBE-NESTING depth, what `dCapᶜ`'s
--      `suc (cSize c)` gas is for deliveries — and `d`, the DEPTH FUEL,
--      is what pays for re-reading it (the re-read returns k LARGER, so
--      k cannot also be the descending argument).
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
--      other, and `opIterD` (Rx.Evaluator) pays it.
--
-- § 3  THE HIERARCHY IS NO LONGER MIRRORED HERE — IT IS LANDED, and
--      this probe now gates the REAL one.  `fLvlD` / `sIterD` / `sLvlD`
--      / `opIterD` / `fIterD` live in Rx.Evaluator (abstract, for the
--      normalisation reason written at them) with their clause
--      equations, and .Caps proves every transformer inflationary and
--      monotone in all five arguments.  The draft mirror that used to
--      sit here — the INHERITED `K` family, whose budget descended
--      instead of being re-read — is gone: it is refuted
--      (agda/probe/Nest-Budget-Probe.agda § 3) and superseded, and a
--      second copy of a landed family is exactly the fat the repo does
--      not keep.  So § 5 below is stated against the definitions the
--      grind will actually consume, not against a look-alike.
--
-- § 4  THE GATE is likewise landed: `fLvl≤fLvlD` (.Caps) says the new
--      per-frame level dominates the old one pointwise at EVERY depth
--      fuel, including d = 0, so every consumer above `fLvl` — `iterL`,
--      `dLvl`, `lvls`, `sizeCount`, the count gate, the whole
--      Level-Walk-Probe ladder — follows by the monotonicity lemmas
--      already proven, with no arithmetic re-derived and no measured row
--      re-run.  `Caps-Face.face-lift` is that gate's first consumer.
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
--      EVERY ONE OF THEM HOLDS AT A FIXED DEPTH FUEL `d`, which is the
--      other half of what the port re-checked.  One subscribe's whole
--      operator walk — its payloads, its nested subscribes, its
--      pushBurst frames — runs at the SAME d; the fuel is spent only by
--      `fIterD`'s step into `fLvlD S W d`, i.e. only when a frame
--      re-reads the budget at its own level.  So the four steps below
--      quantify d and never touch it, exactly as they quantify S and W.
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
-- THE REAL DEFINITIONS, off the tree rather than off a copy.  The
-- budgeted per-frame hierarchy is landed in Rx.Evaluator and its three
-- properties are proven in .Caps, so this probe adds arithmetic ON TOP
-- of them instead of re-deriving a look-alike.  The tree is already
-- built by the time a probe runs, so this costs interface loads only
------------------------------------------------------------------

open import Rx.Evaluator
  using (foldStep; sizeAt; widAt; fCharge;
         fLvlD; sIterD; sLvlD; opIterD; fIterD;
         fLvlD-suc; sIterD-suc; opIterD-suc)

open import Verify-Budget-Sufficient.Caps
  using (widAt-mono;
         sLvlD-infl; opIterD-infl; fIterD-infl;
         sIterD-mono; sLvlD-mono; opIterD-mono; fIterD-mono)

------------------------------------------------------------------
-- § 5  THE COMPOSITION GATE — one lemma per clause SHAPE of the ground
-- tree.  Each takes the receipts as abstract numbers under exactly the
-- bound its own sub-companion reports, and lands the clause's total
-- inside the transformer.  These are the arithmetic steps the step-2
-- grind consumes; the shape is right precisely because they go through
-- with the pieces the clauses already hand back, and the first draft's
-- shape admitted none of them.
--
-- The functions being abstract costs one `≤-reflexive` per lemma: the
-- goal's `suc`-argument has to be opened by hand through the clause
-- equation (`sIterD-suc`, `opIterD-suc`) rather than by reduction.
------------------------------------------------------------------

-- ONE PAYLOAD of a thruWalk / concatDrain: the head subscribes an inner
-- under one more frame (`subscribeInner-caps` recurses at `suc j`), and
-- the tail is the walk's own IH at the level the head left
walk-step : ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  j + j₁ ≤ sLvlD S W d k (suc j) →
  (j + j₁) + j₂ ≤ sIterD S W d k m (j + j₁) →
  j + (j₁ + j₂) ≤ sIterD S W d k (suc m) j
walk-step S W d k m j j₁ j₂ 2≤S hd tl =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₁ j₂))) tl)
                   (sIterD-mono m m d d k k 2≤S ≤-refl ≤-refl hd ≤-refl ≤-refl ≤-refl))
          (≤-reflexive (sym (sIterD-suc S W d k m j)))

-- ONE FRAME, and this is the step the REFRESH buys: the frame's own
-- receipt (`fCharge`, what the ground frame clauses pay) and then its
-- payload walk under the budget READ HERE, at this frame's own level.
-- No inherited `k` appears anywhere in it — that is the whole content
-- of the refresh, and one unit of depth fuel is its price
frame-step : ∀ (S W d j j₀ j₁ : ℕ) → 2 ≤ S →
  j₀ ≤ fCharge S W j →
  (j + j₀) + j₁ ≤ sIterD S W d (suc (sizeAt S j)) (suc (widAt S W j)) (j + j₀) →
  j + (j₀ + j₁) ≤ fLvlD S W (suc d) j
frame-step S W d j j₀ j₁ 2≤S rcpt walk =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₀ j₁))) walk)
                   (sIterD-mono (suc (widAt S W j)) (suc (widAt S W j)) d d
                      (suc (sizeAt S j)) (suc (sizeAt S j)) 2≤S ≤-refl ≤-refl
                      (+-monoʳ-≤ j rcpt) ≤-refl ≤-refl ≤-refl))
          (≤-reflexive (sym (fLvlD-suc S W d j)))

-- ONE OPERATOR, map / take / *All shape: one j for the frame the chain
-- gains, the SOURCE's subscribe at `suc j`, then pushBurst's frames at
-- the level that subscribe left
op-step : ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  suc j + j₁ ≤ opIterD S W d k m (suc j) →
  (suc j + j₁) + j₂ ≤ fIterD S W d k (suc (widAt S W (suc j + j₁))) (suc j + j₁) →
  j + suc (j₁ + j₂) ≤ opIterD S W d k (suc m) j
op-step S W d k m j j₁ j₂ 2≤S src pb =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (trans (+-suc j (j₁ + j₂))
                                                (cong suc (sym (+-assoc j j₁ j₂)))))
                            pb)
                   (fIterD-mono (suc (widAt S W (suc j + j₁))) (suc (widAt S W X))
                      d d k k 2≤S ≤-refl ≤-refl A≤X ≤-refl ≤-refl
                      (s≤s (widAt-mono 2≤S ≤-refl ≤-refl A≤X))))
          (≤-reflexive (sym (opIterD-suc S W d k m j)))
  where
  J₀ = suc (j + suc (sizeAt S j) * suc (sizeAt S j))
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  sucj≤J₁ : suc j ≤ sLvlD S W d k J₀
  sucj≤J₁ = ≤-trans (s≤s (m≤m+n j (suc (sizeAt S j) * suc (sizeAt S j))))
                    (sLvlD-infl S W d k J₀)
  A≤X : suc j + j₁ ≤ X
  A≤X = ≤-trans src (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl sucj≤J₁
                       ≤-refl ≤-refl ≤-refl)

-- ONE OPERATOR, scan shape: an EVAL receipt first (`evalSeed-caps`,
-- `suc (sizeᵗ z)`, so at most `suc (sizeAt S j)`), then the same three
op-step-eval : ∀ (S W d k m j j₀ j₁ j₂ : ℕ) → 2 ≤ S →
  j₀ ≤ suc (sizeAt S j) →
  suc (j + j₀) + j₁ ≤ opIterD S W d k m (suc (j + j₀)) →
  (suc (j + j₀) + j₁) + j₂
    ≤ fIterD S W d k (suc (widAt S W (suc (j + j₀) + j₁))) (suc (j + j₀) + j₁) →
  j + (j₀ + suc (j₁ + j₂)) ≤ opIterD S W d k (suc m) j
op-step-eval S W d k m j j₀ j₁ j₂ 2≤S hj₀ src pb =
  ≤-trans (≤-trans (≤-trans (≤-reflexive
                              (trans (sym (+-assoc j j₀ (suc (j₁ + j₂))))
                                (trans (+-suc (j + j₀) (j₁ + j₂))
                                       (cong suc (sym (+-assoc (j + j₀) j₁ j₂))))))
                            pb)
                   (fIterD-mono (suc (widAt S W (suc (j + j₀) + j₁)))
                      (suc (widAt S W X)) d d k k 2≤S ≤-refl ≤-refl A≤X ≤-refl ≤-refl
                      (s≤s (widAt-mono 2≤S ≤-refl ≤-refl A≤X))))
          (≤-reflexive (sym (opIterD-suc S W d k m j)))
  where
  J₀ = suc (j + suc (sizeAt S j) * suc (sizeAt S j))
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  seed≤ : suc (j + j₀) ≤ sLvlD S W d k J₀
  seed≤ = ≤-trans (s≤s (+-monoʳ-≤ j
                    (≤-trans hj₀ (m≤m*n (suc (sizeAt S j)) (suc (sizeAt S j))))))
                  (sLvlD-infl S W d k J₀)
  A≤X : suc (j + j₀) + j₁ ≤ X
  A≤X = ≤-trans src (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl seed≤
                       ≤-refl ≤-refl ≤-refl)

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
op-step-mu : ∀ (S W d k m j m₀ j₁ : ℕ) → 2 ≤ S →
  m₀ ≤ sizeAt S j →
  (j + (m₀ + suc (m₀ * m₀))) + j₁ ≤ sLvlD S W d k (j + (m₀ + suc (m₀ * m₀))) →
  j + ((m₀ + suc (m₀ * m₀)) + j₁) ≤ opIterD S W d k (suc m) j
op-step-mu S W d k m j m₀ j₁ 2≤S hm₀ sub =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j (m₀ + suc (m₀ * m₀)) j₁)))
                            sub)
                   (≤-trans (sLvlD-mono d d k k 2≤S ≤-refl ≤-refl quad ≤-refl ≤-refl)
                            (≤-trans (opIterD-infl S W d k m (sLvlD S W d k J₀))
                                     (fIterD-infl S W d k (suc (widAt S W X)) X))))
          (≤-reflexive (sym (opIterD-suc S W d k m j)))
  where
  B  = sizeAt S j
  J₀ = suc (j + suc B * suc B)
  X  = opIterD S W d k m (sLvlD S W d k J₀)
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
