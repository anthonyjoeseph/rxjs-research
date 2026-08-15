------------------------------------------------------------------
-- THE COMPOSITION GATE: one lemma per clause SHAPE of the subscribe
-- clique, and the two conversions the OPERATOR COUNT needs.
--
-- Step C gives each member of the clique a conjunct bounding the level
-- it LEAVES.  The arithmetic that lands each clause's total inside its
-- transformer is proven here, ahead of the grind and against the
-- receipts as ABSTRACT NUMBERS under exactly the bound the ground
-- clauses hand back — so a clause proof applies one of these and does no
-- arithmetic of its own.  The shape is right precisely because the
-- clauses go through with the pieces they already have; an earlier draft
-- of the hierarchy admitted none of the four (it ran the frames before
-- the rest of the operator chain, it charged a payload's subscribe at J
-- rather than at `suc J`, and its eval receipt was linear where
-- `unfoldμ-caps` pays `m + suc (m * m)`).
--
-- EVERY ONE OF THEM HOLDS AT A FIXED DEPTH FUEL `d`.  One subscribe's
-- whole operator walk — its payloads, its nested subscribes, its
-- pushBurst frames — runs at the SAME d; the fuel is spent only by
-- `fIterD`'s step into `fLvlD S W d`, i.e. only when a frame re-reads
-- the budget at its own level.  So the steps below quantify d and never
-- touch it, exactly as they quantify S and W.
--
-- AND THE MEMBERS REPORT AT AN INDEX, not at the transformer their own
-- entry is priced by.  A fresh subscribe at level J on budget `suc k` is
-- priced by `sLvlD S W d (suc k) J`, an operator sweep long enough for a
-- whole chain; the gate's operator step consumes its SOURCE's receipt at
-- `opIterD S W d k m (suc j)` — the sweep with m operators LEFT — and m
-- descends by one per operator.  So the recursive call inside an
-- operator clause is not a fresh entry but the same sweep, one shorter,
-- and the conversion the grind would need in the other direction is
-- REFUTED (Chain-Index-Probe (DELETED; git history) § 1: it asks that a sweep
-- sized for a whole chain fit inside the operators the caller has
-- remaining, and at zero operators left the walk transformer is the
-- identity, so the entry sweep — which is strictly above the level —
-- cannot fit).  For the OPERATOR COUNT the grind uses `chain-desc`
-- (§ 3) for the descent and a bare `s≤s` for the fresh-entry case (both
-- are inline at every site and need no conversion lemma).  § 2 below is
-- the WIDTH-INDEX pair: `walk-index` (sIterD monotone in the payload
-- count) and `burst-index` (fIterD monotone in the emit count).
--
-- This module is not mutual with any of them — it consumes the `-mono`
-- and `-infl` families as finished facts — so it is its own compilation
-- unit and the clique imports it.  The transformers being abstract costs
-- one `≤-reflexive` per lemma: the goal's `suc`-argument has to be
-- opened by hand through the clause equation (`sIterD-suc`,
-- `opIterD-suc`) rather than by reduction.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Caps-Chain where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-suc; +-assoc; +-identityʳ; +-comm;
         +-mono-≤; +-monoʳ-≤; +-monoˡ-≤; *-mono-≤; *-suc; n≤1+n;
         m≤m+n; m≤n+m; m≤m*n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Evaluator
  using (sizeAt; widAt; fCharge; fLvl;
         fLvlD; sIterD; sLvlD; opIterD; fIterD;
         fLvlD-0; fLvlD-suc; sIterD-suc; sLvlD-suc; opIterD-suc;
         fIterD-suc; fIterD-0; sIterD-0)
open import Verify-Budget-Sufficient.Caps
  using (widAt-mono; iterSize-infl;
         fLvlD-infl; sLvlD-infl; opIterD-infl; fIterD-infl; sIterD-infl;
         sIterD-mono; sLvlD-mono; opIterD-mono; fIterD-mono)
-- the payload edge's three rungs are lifted with +1-superadditivity, the
-- only place outside `walk-step-suc` that needs to move a report to a
-- HIGHER entry level rather than to a wider transformer
open import Verify-Budget-Sufficient.Caps-Sadd using (opIterD-sadd; sIterD-sadd)

------------------------------------------------------------------
-- § 1.  THE FIVE CLAUSE SHAPES.
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

-- and an empty payload list leaves the level where it found it
walk-nil : ∀ (S W d k j : ℕ) → j + 0 ≤ sIterD S W d k 0 j
walk-nil S W d k j =
  ≤-trans (≤-reflexive (+-identityʳ j)) (≤-reflexive (sym (sIterD-0 S W d k j)))

-- a dry payload subscribe, which does not move the level either
inner-nil : ∀ (S W d k j : ℕ) → suc (j + 0) ≤ sLvlD S W d k (suc j)
inner-nil S W d k j =
  ≤-trans (≤-reflexive (cong suc (+-identityʳ j))) (sLvlD-infl S W d k (suc j))

-- and a leaf subscribe: no operator is entered, so the sweep is
-- inflationary and nothing else is owed
leaf-lvl : ∀ (S W d k m j : ℕ) → j + 0 ≤ opIterD S W d k m j
leaf-lvl S W d k m j =
  ≤-trans (≤-reflexive (+-identityʳ j)) (opIterD-infl S W d k m j)

-- ONE EMIT of a pushBurst, and it is the fIterD twin of `walk-step`:
-- the emit is stepped through the ONE frame just built (`stepFrame-caps`,
-- which reports the level that frame LEAVES) and the rest of the burst
-- runs from there.  The gate had no fIterD row at all — .Caps-Face's pass
-- memo (~6090) names both this and `burst-index` below as what the
-- signature pass would need, and `pushBurst-caps` is the head that needs
-- them: it recurses on `em ∷ ems`, so its index is the EMIT COUNT
burst-step : ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  j + j₁ ≤ fLvlD S W d j →
  (j + j₁) + j₂ ≤ fIterD S W d k m (j + j₁) →
  j + (j₁ + j₂) ≤ fIterD S W d k (suc m) j
burst-step S W d k m j j₁ j₂ 2≤S hd tl =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₁ j₂))) tl)
                   (fIterD-mono m m d d k k 2≤S ≤-refl ≤-refl hd ≤-refl ≤-refl ≤-refl))
          (≤-reflexive (sym (fIterD-suc S W d k m j)))

-- and the empty burst leaves the level where it found it
burst-nil : ∀ (S W d k j : ℕ) → j + 0 ≤ fIterD S W d k 0 j
burst-nil S W d k j =
  ≤-trans (≤-reflexive (+-identityʳ j)) (≤-reflexive (sym (fIterD-0 S W d k j)))

-- ONE FRAME, and this is the step the REFRESH buys: the frame's own
-- receipt (`fCharge`, what the ground frame clauses pay) and then its
-- payload walk under the budget READ HERE, at this frame's own level.
-- No inherited `k` appears anywhere in it — that is the whole content
-- of the refresh, and one unit of depth fuel is its price
frame-step : ∀ (S W d j j₀ j₁ : ℕ) → 2 ≤ S →
  j₀ ≤ fCharge S W j →
  (j + j₀) + j₁
    ≤ sIterD S W d (suc (sizeAt S (suc j))) (suc (widAt S W j)) (j + j₀) →
  j + (j₀ + j₁) ≤ fLvlD S W (suc d) j
frame-step S W d j j₀ j₁ 2≤S rcpt walk =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₀ j₁))) walk)
                   (sIterD-mono (suc (widAt S W j)) (suc (widAt S W j)) d d
                      (suc (sizeAt S (suc j))) (suc (sizeAt S (suc j)))
                      2≤S ≤-refl ≤-refl
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

------------------------------------------------------------------
-- THE DESCENTS — each caller's D-tower budget dominates its callee's,
-- so a hypothesis of the form `budget ≤ L̂` passes DOWN a call chain
-- unchanged.  Consumed by the wet faces' reset-anchor ceiling
-- (.Walk-Level): `Caps.cSize (frameStep L̂ c) ≤ Ŝ` is threaded once,
-- and these convert each face's own budget to its callee's.  Pure
-- D-tower arithmetic: the -suc equations read backwards, each the
-- level-composition lemma above it minus the composition.
------------------------------------------------------------------

-- one operator in: the source sweep at `suc J` sits under the sweep
-- with the operator still unspent (op-step's spine, no fIterD charge)
op-desc : ∀ (S W d k m J : ℕ) → 2 ≤ S →
  opIterD S W d k m (suc J) ≤ opIterD S W d k (suc m) J
op-desc S W d k m J 2≤S =
  ≤-trans (≤-trans (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl sucJ≤J₁
                      ≤-refl ≤-refl ≤-refl)
                   (fIterD-infl S W d k (suc (widAt S W X)) X))
          (≤-reflexive (sym (opIterD-suc S W d k m J)))
  where
  J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  sucJ≤J₁ : suc J ≤ sLvlD S W d k J₀
  sucJ≤J₁ = ≤-trans (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J))))
                    (sLvlD-infl S W d k J₀)

-- the push after the source subscribe: given the source's level report
-- and the emit-count bound, the whole fIterD charge sits under the
-- operator sweep (op-step's tail, the level report left un-composed)
push-desc : ∀ (S W d k m n J j₁ : ℕ) → 2 ≤ S →
  suc J + j₁ ≤ opIterD S W d k m (suc J) →
  n ≤ suc (widAt S W (suc J + j₁)) →
  fIterD S W d k n (suc J + j₁) ≤ opIterD S W d k (suc m) J
push-desc S W d k m n J j₁ 2≤S src cnt =
  ≤-trans (≤-trans (burst-index′ 2≤S cnt)
                   (fIterD-mono (suc (widAt S W (suc J + j₁))) (suc (widAt S W X))
                      d d k k 2≤S ≤-refl ≤-refl A≤X ≤-refl ≤-refl
                      (s≤s (widAt-mono 2≤S ≤-refl ≤-refl A≤X))))
          (≤-reflexive (sym (opIterD-suc S W d k m J)))
  where
  J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  sucJ≤J₁ : suc J ≤ sLvlD S W d k J₀
  sucJ≤J₁ = ≤-trans (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J))))
                    (sLvlD-infl S W d k J₀)
  A≤X : suc J + j₁ ≤ X
  A≤X = ≤-trans src (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl sucJ≤J₁
                       ≤-refl ≤-refl ≤-refl)
  burst-index′ : 2 ≤ S → n ≤ suc (widAt S W (suc J + j₁)) →
    fIterD S W d k n (suc J + j₁)
      ≤ fIterD S W d k (suc (widAt S W (suc J + j₁))) (suc J + j₁)
  burst-index′ h hm =
    fIterD-mono n (suc (widAt S W (suc J + j₁))) d d k k h
      ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hm

-- one frame in: the frame's own level allowance sits under any
-- nonempty burst charge (burst-step's spine, no tail)
frame-desc : ∀ (S W d k m J : ℕ) →
  fLvlD S W d J ≤ fIterD S W d k (suc m) J
frame-desc S W d k m J =
  ≤-trans (fIterD-infl S W d k m (fLvlD S W d J))
          (≤-reflexive (sym (fIterD-suc S W d k m J)))

-- and the tail of the burst, from the level the head frame left
-- (burst-step minus the composition)
tail-desc : ∀ (S W d k m J j₁ : ℕ) → 2 ≤ S →
  J + j₁ ≤ fLvlD S W d J →
  fIterD S W d k m (J + j₁) ≤ fIterD S W d k (suc m) J
tail-desc S W d k m J j₁ 2≤S hd =
  ≤-trans (fIterD-mono m m d d k k 2≤S ≤-refl ≤-refl hd ≤-refl ≤-refl ≤-refl)
          (≤-reflexive (sym (fIterD-suc S W d k m J)))

-- ONE sLvlD ADVANCE sits within the matching sIterD step — the same
-- -suc/-infl two-liner as frame-desc/tail-desc.  Used at every element
-- of a thruWalk loop in the wet walk face.
walk-desc : ∀ (S W d k m j : ℕ) →
  sLvlD S W d k (suc j) ≤ sIterD S W d k (suc m) j
walk-desc S W d k m j =
  ≤-trans (sIterD-infl S W d k m (sLvlD S W d k (suc j)))
          (≤-reflexive (sym (sIterD-suc S W d k m j)))

-- ACTUAL INNER OPS ≤ sLvlD MAX.  The inner subscribe at position suc j
-- runs at most suc (sizeAt S (suc j)) operators (the size cap at that
-- level); opIterD-mono + sLvlD-suc land the actual count under the max.
inner-desc : ∀ (S W d bud j m : ℕ) → 2 ≤ S →
  suc m ≤ suc (sizeAt S (suc j)) →
  opIterD S W d bud (suc m) (suc j) ≤ sLvlD S W d (suc bud) (suc j)
inner-desc S W d bud j m 2≤S hm =
  ≤-trans (opIterD-mono (suc m) (suc (sizeAt S (suc j))) d d bud bud
             2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hm)
          (≤-reflexive (sym (sLvlD-suc S W d bud (suc j))))

-- B + suc (B · B) ≤ suc B · suc B — the arithmetic the μ receipt needs,
-- and the reason the per-operator eval receipt is a SQUARE
quad-arith : ∀ (B : ℕ) → B + suc (B * B) ≤ suc B * suc B
quad-arith B =
  ≤-trans (≤-reflexive (+-suc B (B * B)))
          (≤-trans (s≤s (+-monoʳ-≤ B (m≤n+m (B * B) B)))
                   (≤-reflexive (sym (cong (λ x → suc (B + x)) (*-suc B B)))))

-- ANY EDGE THAT ENTERS A FRESH SUBSCRIBE, with its receipt abstracted.
-- This is the shape the μ step was first written in, and it is not about
-- μ: the proof spends the premise, then `sLvlD-mono` under a bound
-- showing the receipt FITS the room `opIterD … (suc m) j` opens, then two
-- `-infl` steps, then the clause equation.  Only that bound mentions the
-- edge at all, so it becomes a hypothesis and the μ unfolding, the share
-- connect and any other fresh entry are instances rather than copies.
-- The room is QUADRATIC in the level's size cap, which is why any receipt
-- a clause can actually pay fits inside it
op-step-entry : ∀ (S W d k m j r j₁ : ℕ) → 2 ≤ S →
  j + r ≤ suc (j + suc (sizeAt S j) * suc (sizeAt S j)) →
  (j + r) + j₁ ≤ sLvlD S W d k (j + r) →
  j + (r + j₁) ≤ opIterD S W d k (suc m) j
op-step-entry S W d k m j r j₁ 2≤S fits sub =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j r j₁))) sub)
                   (≤-trans (sLvlD-mono d d k k 2≤S ≤-refl ≤-refl fits ≤-refl ≤-refl)
                            (≤-trans (opIterD-infl S W d k m (sLvlD S W d k J₀))
                                     (fIterD-infl S W d k (suc (widAt S W X)) X))))
          (≤-reflexive (sym (opIterD-suc S W d k m j)))
  where
  B  = sizeAt S j
  J₀ = suc (j + suc B * suc B)
  X  = opIterD S W d k m (sLvlD S W d k J₀)

-- THE μ OPERATOR: the unfolding receipt `m₀ + suc (m₀ * m₀)`, and then a
-- FRESH subscribe on a LARGER term — which is why it is charged as one
-- NESTING level rather than as a continuation of the same chain, and
-- why the budget k has to count μ-nesting as well as *All-nesting.  Its
-- whole content is now the `fits` argument: the quadratic receipt inside
-- the quadratic room
op-step-mu : ∀ (S W d k m j m₀ j₁ : ℕ) → 2 ≤ S →
  m₀ ≤ sizeAt S j →
  (j + (m₀ + suc (m₀ * m₀))) + j₁ ≤ sLvlD S W d k (j + (m₀ + suc (m₀ * m₀))) →
  j + ((m₀ + suc (m₀ * m₀)) + j₁) ≤ opIterD S W d k (suc m) j
op-step-mu S W d k m j m₀ j₁ 2≤S hm₀ =
  op-step-entry S W d k m j (m₀ + suc (m₀ * m₀)) j₁ 2≤S quad
  where
  B  = sizeAt S j
  quad : j + (m₀ + suc (m₀ * m₀)) ≤ suc (j + suc B * suc B)
  quad = ≤-trans (+-monoʳ-≤ j (≤-trans (+-mono-≤ hm₀ (s≤s (*-mono-≤ hm₀ hm₀)))
                                       (quad-arith B)))
                 (n≤1+n (j + suc B * suc B))

-- THE SHARE CONNECT: the receipt is 1, the registration for the joining
-- subscriber, and its `fits` is free — one registration sits inside the
-- quadratic room at every cap.  Stated at `suc j` rather than at `j + 1`
-- because that is the shape a clause presents, and `_+_` recursing on its
-- FIRST argument leaves `j + 1` stuck: the conversion belongs here once
-- rather than at every call site
share-fits : ∀ (S j : ℕ) → j + 1 ≤ suc (j + suc (sizeAt S j) * suc (sizeAt S j))
share-fits S j =
  ≤-trans (≤-reflexive (+-comm j 1))
          (s≤s (m≤m+n j (suc (sizeAt S j) * suc (sizeAt S j))))

op-step-share : ∀ (S W d k m j j₁ : ℕ) → 2 ≤ S →
  suc j + j₁ ≤ sLvlD S W d k (suc j) →
  j + suc j₁ ≤ opIterD S W d k (suc m) j
op-step-share S W d k m j j₁ 2≤S sub =
  op-step-entry S W d k m j 1 j₁ 2≤S (share-fits S j)
    (subst (λ x → x + j₁ ≤ sLvlD S W d k x) (sym (+-comm j 1)) sub)

------------------------------------------------------------------
-- § 2.  THE INDEX.
------------------------------------------------------------------

-- AND THE WALK'S OWN INDEX IS THE PAYLOAD COUNT.  `sIterD S W d k m J`
-- prices m payloads in sequence, so a walk's conjunct reads
-- `m = length vals` while `frame-step` above consumes the walk at
-- `suc (widAt S W j)`.  Those meet by monotonicity in the index, on the
-- length the caller has in hand — `valsCaps?`'s length conjunct, whose
-- cap `Caps.cWid (frameStep j c)` IS `widAt (cSize c) (cWid c) j`
-- definitionally, so no arithmetic sits between the two
walk-index : ∀ (S W d k m j J : ℕ) → 2 ≤ S → m ≤ suc (widAt S W j) →
  sIterD S W d k m J ≤ sIterD S W d k (suc (widAt S W j)) J
walk-index S W d k m j J 2≤S hm =
  sIterD-mono m (suc (widAt S W j)) d d k k 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hm

-- AND THE BURST'S OWN INDEX IS THE EMIT COUNT, met the same way: on the
-- length `burstCount?` already carries (`countLen`), whose cap
-- `Caps.cWid (frameStep j c)` IS `widAt (cSize c) (cWid c) j`
-- definitionally, so nothing sits between the receipt and the index
burst-index : ∀ (S W d k m j J : ℕ) → 2 ≤ S → m ≤ suc (widAt S W j) →
  fIterD S W d k m J ≤ fIterD S W d k (suc (widAt S W j)) J
burst-index S W d k m j J 2≤S hm =
  fIterD-mono m (suc (widAt S W j)) d d k k 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hm

------------------------------------------------------------------
-- § 3.  AND THE INDEX DESCENDS ACROSS A CHAIN EDGE.
--
-- `op-step` concludes at `suc m`, so an operator clause can only report
-- if its own index is a SUCCESSOR — which means every clause that
-- recurses splits its index, and hands the source the predecessor.
-- `chain-desc` is what the source's hypothesis costs at that handoff.
--
-- The clause holds `suc (sizeᵉ TERM) ≤ suc m′` and owes
-- `suc (sizeᵉ SOURCE) ≤ m′`, and every chain constructor's size is
-- `suc (head + source)` (Rx.Exp:466-475), so ONE lemma covers the whole
-- family: `hd := sizeᵗ f` for map and take, `hd := sizeᵗ f + sizeᵗ z`
-- for scan (`+` associates left, so its head being a sum costs no
-- rewrite), and `hd := 0` for the headless six (mergeAll, concatAll,
-- switchAll, exhaustAll, μ, defer), where `0 + src` reduces to `src`
-- definitionally and the lemma degenerates to `≤-pred`.
--
-- The zero case needs nothing at all: `suc x ≤ zero` is uninhabited by
-- CONSTRUCTOR — neither `z≤n` nor `s≤s` can build it — so the split's
-- other half is an absurd pattern whatever the stuck head term is, and
-- costs one line per clause rather than a proof.
chain-desc : ∀ (hd src m′ : ℕ) → suc (suc (hd + src)) ≤ suc m′ → suc src ≤ m′
chain-desc hd src m′ (s≤s h) = ≤-trans (s≤s (m≤n+m src hd)) h

------------------------------------------------------------------
-- § 4.  THE STRICT PAYLOAD BOUND, for the one clause that reports a
-- witness for its CARDINALITY rather than for anything it subscribed.
--
-- `thruConsume-caps`'s concat-queue push grows a queue whose LENGTH
-- `widNode` bounds, so the cons has to be paid for with a level, and its
-- conjunct lands at `suc (j + 1)` where every other clause of that head
-- lands at `suc (j + 0)`.  `inner-nil` cannot serve it: the nil lemma
-- reaches `suc j` exactly, and this needs room STRICTLY above it.
--
-- AND THE STATEMENT IS FALSE AT A ZERO BUDGET — `sLvlD S W d 0 J` is `J`
-- on the nose, so the goal would ask `suc (suc j) ≤ suc j`
-- (machine-refuted, Queue-Push-Probe (DELETED; git history) § 1).  So the level
-- is bought with the budget's POSITIVITY — and since the walk heads now
-- report at `suc bud`, that positivity is a literal `s≤s z≤n` at the
-- clause.  It used to be earned from a head's `nest … ≤ bud` hypothesis
-- through a `1≤nest` lemma; reporting at the successor retired both.
opIterD-strict : ∀ (S W d k m J : ℕ) → suc J ≤ opIterD S W d k (suc m) J
opIterD-strict S W d k m J =
  let J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
      J₂ = opIterD S W d k m (sLvlD S W d k J₀)
  in ≤-trans (≤-trans (≤-trans (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J))))
                               (≤-trans (sLvlD-infl S W d k J₀)
                                        (opIterD-infl S W d k m (sLvlD S W d k J₀))))
                      (fIterD-infl S W d k (suc (widAt S W J₂)) J₂))
             (≤-reflexive (sym (opIterD-suc S W d k m J)))

-- and the clause's goal, assembled: the positive-budget equation opens
-- into an `opIterD` whose index is `suc (sizeAt S (suc j))`, already a
-- successor, so the strict step applies with no side condition
queue-push : ∀ (S W d bud j : ℕ) → 1 ≤ bud →
  suc (j + 1) ≤ sLvlD S W d bud (suc j)
queue-push S W d (suc b) j _ =
  subst (λ y → suc y ≤ sLvlD S W d (suc b) (suc j)) (sym (+-comm j 1))
        (≤-trans (opIterD-strict S W d b (sizeAt S (suc j)) (suc j))
                 (≤-reflexive (sym (sLvlD-suc S W d b (suc j)))))

------------------------------------------------------------------
-- § 5.  THE PAYLOAD EDGE, and the three rungs it has to clear.
--
-- `subscribeInner-caps`'s conjunct is the one every clause of
-- `thruConsume-caps` projects, so it stands under that whole head.  Its
-- shape is forced from both sides: its CONSUMER is `walk-step-suc`,
-- whose first premise is `suc (j + j₁) ≤ sLvlD S W d k (suc j)`, and its
-- own witness is `suc (suc (suc j₂))` because the clause's caps live at
-- `frameStep (j + suc (suc (suc j₂)))` — the `splitBurst` square costs
-- TWO levels on top of the inner subscribe's own `suc j + j₂`.
--
-- So the conjunct's left side sits FOUR above `j + j₂` while the IH
-- delivers ONE, and the IH's bound is tight where it lands.  The slack
-- is not in the IH but in `opIterD`'s interior, and `-sadd` is what
-- reaches it: three steps of `suc (F J) ≤ F (suc J)` turn the IH's
-- report into one three levels higher, and `opIterD`'s own `J₀`
-- excursion clears `suc j` by three for free.
--
-- THE INDEX MATTERS.  The IH must be called at `sizeAt S (suc j)`, NOT
-- at its successor: `sLvlD S W d (suc k) (suc j)` opens into `opIterD …
-- (suc (sizeAt S (suc j))) (suc j)`, and it is the step from that index
-- down to its predecessor that exposes the excursion.  Called at the
-- successor the IH lands flush against the target with nothing over,
-- which is exactly why this site resisted closing.
------------------------------------------------------------------

-- the size cap is at least 2 at every level, which the three-rung
-- version needs and the two-rung version would not have: at `B = 0` the
-- square below is 1 and the room is short by one
2≤sizeAt : ∀ (S J : ℕ) → 2 ≤ S → 2 ≤ sizeAt S J
2≤sizeAt S J 2≤S = ≤-trans 2≤S (iterSize-infl S (≤-trans (s≤s z≤n) 2≤S) J S)

-- `J₀ = suc (suc j + suc B * suc B)` clears `suc j` by three.  Stated
-- with the successors on the OUTSIDE because `_+_` recurses on its first
-- argument, which leaves a literal `j + 3` stuck on a variable
J₀-room : ∀ (S j : ℕ) → 2 ≤ S →
  suc (suc (suc (suc j)))
    ≤ suc (suc j + suc (sizeAt S (suc j)) * suc (sizeAt S (suc j)))
J₀-room S j 2≤S =
  s≤s (s≤s (≤-trans (≤-reflexive (sym (+-comm j 2))) (+-monoʳ-≤ j sq)))
  where
  sq : 2 ≤ suc (sizeAt S (suc j)) * suc (sizeAt S (suc j))
  sq = ≤-trans (≤-trans (2≤sizeAt S (suc j) 2≤S) (n≤1+n (sizeAt S (suc j))))
               (m≤m+n (suc (sizeAt S (suc j)))
                      (sizeAt S (suc j) * suc (sizeAt S (suc j))))

inner-step : ∀ (S W d k j j₂ : ℕ) → 2 ≤ S →
  suc j + j₂ ≤ opIterD S W d k (sizeAt S (suc j)) (suc j) →
  suc (j + suc (suc (suc j₂))) ≤ sLvlD S W d (suc k) (suc j)
inner-step S W d k j j₂ 2≤S ih =
  ≤-trans (≤-trans (≤-reflexive shape) climb)
          (≤-reflexive (sym (trans (sLvlD-suc S W d k (suc j))
                                   (opIterD-suc S W d k B (suc j)))))
  where
  B  = sizeAt S (suc j)
  J₀ = suc (suc j + suc B * suc B)
  L  = sLvlD S W d k J₀
  J₂ = opIterD S W d k B L

  shape : suc (j + suc (suc (suc j₂))) ≡ suc (suc (suc (suc (j + j₂))))
  shape = cong suc (trans (+-suc j (suc (suc j₂)))
                          (cong suc (trans (+-suc j (suc j₂))
                                           (cong suc (+-suc j j₂)))))

  lift3 : suc (suc (suc (opIterD S W d k B (suc j))))
            ≤ opIterD S W d k B (suc (suc (suc (suc j))))
  lift3 = ≤-trans (s≤s (≤-trans (s≤s (opIterD-sadd {S} {W} {suc j} B d k 2≤S))
                                (opIterD-sadd {S} {W} {suc (suc j)} B d k 2≤S)))
                  (opIterD-sadd {S} {W} {suc (suc (suc j))} B d k 2≤S)

  climb : suc (suc (suc (suc (j + j₂)))) ≤ fIterD S W d k (suc (widAt S W J₂)) J₂
  climb =
    ≤-trans (≤-trans (≤-trans (s≤s (s≤s (s≤s ih))) lift3)
                     (opIterD-mono B B d d k k 2≤S ≤-refl ≤-refl
                        (≤-trans (J₀-room S j 2≤S) (sLvlD-infl S W d k J₀))
                        ≤-refl ≤-refl ≤-refl))
            (fIterD-infl S W d k (suc (widAt S W J₂)) J₂)

------------------------------------------------------------------
-- § 6.  THE FRAME HEADS' OWN SUPPLIES, which are DEPTH-GENERIC.
--
-- `innerFinish` / `innerReact` / `stepFrame` all report in `fLvlD S W dep
-- j` at an ABSTRACT `dep`, so neither of `fLvlD`'s clauses may be assumed
-- — and `frame-step` above concludes only at `suc d`.  What makes a
-- generic supply possible anyway is that `fLvlD` at zero is NOT the
-- identity the other transformers degenerate to: it is `fLvl S W J + suc
-- (widAt S W J)`, and `fLvl S W J` is `J + fCharge S W J`.  So one
-- frame's own receipt fits under BOTH clauses by inflation alone, with no
-- depth hypothesis anywhere.
--
-- This is the whole reason buckets A and D of the site census do not wait
-- on the depth ruling that site forced (probe module since DELETED): a
-- RECEIPT fits at depth zero, and only a WALK does not.
------------------------------------------------------------------

-- a frame that moves nothing: every clause whose witness is 0
frame-nil : ∀ (S W d j : ℕ) → j + 0 ≤ fLvlD S W d j
frame-nil S W d j = ≤-trans (≤-reflexive (+-identityʳ j)) (fLvlD-infl S W d j)

-- and a frame that pays only its own receipt.  At zero the receipt sits
-- in `fLvl`'s summand with the width still to spare; at `suc d` it sits
-- in the `fLvl` the walk STARTS from, so `sIterD-infl` finishes.  Both
-- branches are inflation — the receipt never needs the walk
frame-recv : ∀ (S W d j j₀ : ℕ) → j₀ ≤ fCharge S W j →
  j + j₀ ≤ fLvlD S W d j
frame-recv S W zero j j₀ h =
  ≤-trans (≤-trans (+-monoʳ-≤ j h)
                   (m≤m+n (j + fCharge S W j) (suc (widAt S W j))))
          (≤-reflexive (sym (fLvlD-0 S W j)))
frame-recv S W (suc d) j j₀ h =
  ≤-trans (≤-trans (+-monoʳ-≤ j h)
                   (sIterD-infl S W d (suc (sizeAt S (suc j)))
                                (suc (widAt S W j)) (fLvl S W j)))
          (≤-reflexive (sym (fLvlD-suc S W d j)))

-- THE LAST PAYLOAD of a walk, where the queue behind it is bounded by
-- inflation rather than by a recursive report.  `walk-step` at `j₂ := 0`,
-- with the `j₁ + 0` its conclusion carries absorbed here once instead of
-- at the clause
walk-last : ∀ (S W d k m j j₁ : ℕ) → 2 ≤ S →
  j + j₁ ≤ sLvlD S W d k (suc j) →
  j + j₁ ≤ sIterD S W d k (suc m) j
walk-last S W d k m j j₁ 2≤S hd =
  ≤-trans (≤-reflexive (cong (j +_) (sym (+-identityʳ j₁))))
          (walk-step S W d k m j j₁ 0 2≤S hd
            (≤-trans (≤-reflexive (+-identityʳ (j + j₁)))
                     (sIterD-infl S W d k m (j + j₁))))

-- AND A WALK THAT HAS NOT SPENT ITS WHOLE PAYLOAD ALLOWANCE HAS ONE
-- LEVEL IN HAND — which is what the concat FINISH needs and the
-- thru-outer frame does not.  Both frames report through `frame-step`,
-- whose walk premise is indexed at the full `suc (widAt S W j)`; a
-- thru-outer's witness is the walk's own j′ and meets it by `walk-index`
-- alone, but `innerFinish-caps`'s concat clause reinstalls the drained
-- node and so reports `suc j′` — one MORE than `concatDrain-caps` hands
-- back.  The room is real, and it is the unused payload slot: the queue
-- is bounded by `widAt S W j` (`widNode`'s length conjunct) while the
-- premise admits `suc (widAt S W j)` payloads, and one payload of a walk
-- is worth at least one level (`sIterD-sadd`, then the entry the next
-- payload starts from, `sLvlD-infl`).  So the drain's report rises by one
-- and the index widens in the same step
walk-room : ∀ (S W d k m j j₁ : ℕ) → 2 ≤ S → m ≤ widAt S W j →
  j + j₁ ≤ sIterD S W d k m j →
  j + suc j₁ ≤ sIterD S W d k (suc (widAt S W j)) j
walk-room S W d k m j j₁ 2≤S hm h =
  ≤-trans (≤-reflexive (+-suc j j₁))
    (≤-trans (≤-trans (s≤s h) (sIterD-sadd {S} {W} {j} m d k 2≤S))
      (≤-trans
        -- one payload's own entry, so the m-fold walk restarts above `suc j`
        (≤-trans (sIterD-mono m m d d k k 2≤S ≤-refl ≤-refl
                    (sLvlD-infl S W d k (suc j)) ≤-refl ≤-refl ≤-refl)
                 (≤-reflexive (sym (sIterD-suc S W d k m j))))
        -- and the slot it used was one the premise had spare
        (sIterD-mono (suc m) (suc (widAt S W j)) d d k k 2≤S
                     ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl (s≤s hm))))

-- j ≤ fLvl S W j, since fLvl S W J = J + fCharge S W J.  The frame's own
-- receipt, absorbed by inflation rather than spent
j≤fLvl : ∀ (S W j : ℕ) → j ≤ fLvl S W j
j≤fLvl S W j = m≤m+n j (fCharge S W j)

-- A DRAIN INSIDE A FRAME, which is `walk-room` carried the rest of the
-- way home.  `concatDrain-caps` reports its walk in `sIterD` currency at
-- the budget the frame RE-READ; the enclosing `innerFinish-caps` has to
-- report in `fLvlD` at one higher depth, and this is that conversion.
--
-- Note what does NOT appear: `frame-step`, and any explicit `fCharge`
-- receipt.  The `suc j₁` is already what `walk-room` buys — one spare
-- payload slot is worth one level — and `fLvlD`'s own base point
-- `fLvl S W j` absorbs the frame's charge by plain inflation.  So the
-- frame pays for itself out of the room the queue did not use.
--
-- `hk` is FREE at the call site rather than an extra burden: a frame
-- hands its drain the REFRESHED budget `sizeAt S (suc j)`, exactly as
-- `stepFrame-caps`'s thru-outer clause hands `thruWalk-caps` the same
-- thing, so the reported `k` IS `frameBud c j = suc (sizeAt S (suc j))`
-- and `hk` is `≤-refl`
concat-frame : ∀ (S W d k m j j₁ : ℕ) → 2 ≤ S →
  m ≤ widAt S W j →
  k ≤ suc (sizeAt S (suc j)) →
  j + j₁ ≤ sIterD S W d k m j →
  j + suc j₁ ≤ fLvlD S W (suc d) j
concat-frame S W d k m j j₁ 2≤S hm hk h =
  ≤-trans
    (≤-trans
      -- the queue-length index up to the full `suc (widAt S W j)`
      (walk-room S W d k m j j₁ 2≤S hm h)
      -- `k` up to the budget `fLvlD`'s `suc d` clause reads
      (sIterD-mono (suc (widAt S W j)) (suc (widAt S W j)) d d k
         (suc (sizeAt S (suc j))) 2≤S ≤-refl ≤-refl ≤-refl ≤-refl hk ≤-refl))
    (≤-trans
      -- and the entry level from `j` up to `fLvl S W j`
      (sIterD-mono (suc (widAt S W j)) (suc (widAt S W j)) d d
         (suc (sizeAt S (suc j))) (suc (sizeAt S (suc j))) 2≤S ≤-refl ≤-refl
         (j≤fLvl S W j) ≤-refl ≤-refl ≤-refl)
      (≤-reflexive (sym (fLvlD-suc S W d j))))

------------------------------------------------------------------
-- § 7.  THE TWO ENTRIES THAT SUBSCRIBE NOTHING.
--
-- A literal burst and a parked body are both ENTRIES with a receipt and
-- no continuation: neither runs a source, so neither has the `suc (j₁ +
-- j₂)` tail that `op-step` and `op-step-eval` consume, and their
-- witnesses are FLAT.  `op-step-entry` at `j₁ := 0` is the gate for
-- both, with `sLvlD-infl` for its subscribe premise and the `+ 0` its
-- conclusion carries absorbed here rather than at the clause.
--
-- `ofᵉ` is the one that needed new arithmetic: `op-step-entry`'s room is
-- quadratic in the size cap and its receipt is linear, but the fit is
-- not free — it needs the cap to be at least 2, exactly as the payload
-- edge's three rungs did.  `2≤sizeAt` pays for it.  `deferᵉ` needs
-- nothing new: its receipt is 1 and `share-fits` already covers that.
------------------------------------------------------------------

-- the literal burst's receipt fits the entry's room, with room to spare
of-fits : ∀ (S j j₀ : ℕ) → 2 ≤ S → j₀ ≤ sizeAt S j →
  j + (j₀ + 3) ≤ suc (j + suc (sizeAt S j) * suc (sizeAt S j))
of-fits S j j₀ 2≤S hj₀ =
  ≤-trans (+-monoʳ-≤ j room) (≤-reflexive (+-suc j (B′ * B′)))
  where
  B  = sizeAt S j
  B′ = suc B

  widen : B + 3 ≤ B + B′
  widen = +-monoʳ-≤ B (s≤s (2≤sizeAt S j 2≤S))

  square : B + B′ ≤ B′ * B′
  square = ≤-trans (≤-reflexive (+-suc B B))
                   (+-monoʳ-≤ B′ (m≤m*n B B′))

  room : j₀ + 3 ≤ suc (B′ * B′)
  room = ≤-trans (≤-trans (≤-trans (+-monoˡ-≤ 3 hj₀) widen) square)
                 (n≤1+n (B′ * B′))

-- ONE LITERAL BURST: the eval receipt, and nothing after it
of-step : ∀ (S W d k m j j₀ : ℕ) → 2 ≤ S → j₀ ≤ sizeAt S j →
  j + (j₀ + 3) ≤ opIterD S W d k (suc m) j
of-step S W d k m j j₀ 2≤S hj₀ =
  ≤-trans (≤-reflexive (cong (j +_) (sym (+-identityʳ (j₀ + 3)))))
          (op-step-entry S W d k m j (j₀ + 3) 0 2≤S
            (of-fits S j j₀ 2≤S hj₀)
            (≤-trans (≤-reflexive (+-identityʳ (j + (j₀ + 3))))
                     (sLvlD-infl S W d k (j + (j₀ + 3)))))

-- ONE PARKED BODY: the registration, whose room `share-fits` pays free
defer-step : ∀ (S W d k m j : ℕ) → 2 ≤ S →
  j + 1 ≤ opIterD S W d k (suc m) j
defer-step S W d k m j 2≤S =
  op-step-share S W d k m j 0 2≤S
    (≤-trans (≤-reflexive (+-identityʳ (suc j)))
             (sLvlD-infl S W d k (suc j)))

-- THE SHARE CONNECT'S OWN EDGE, which is the payload edge minus one rung.
-- `sharedConnect-caps` prepends ONE emit to the burst its recursive
-- subscribe returned, where a payload subscribe's `splitBurst` square
-- costs two — so its witness is `suc (suc j₂)` against the payload's
-- `suc (suc (suc j₂))`, off the SAME IH.  A smaller left side under the
-- same bound is just monotonicity, so this costs one step and no new
-- excursion: `inner-step` already bought the room
connect-step : ∀ (S W d k j j₂ : ℕ) → 2 ≤ S →
  suc j + j₂ ≤ opIterD S W d k (sizeAt S (suc j)) (suc j) →
  suc (j + suc (suc j₂)) ≤ sLvlD S W d (suc k) (suc j)
connect-step S W d k j j₂ 2≤S ih =
  ≤-trans (s≤s (+-monoʳ-≤ j (n≤1+n (suc (suc j₂)))))
          (inner-step S W d k j j₂ 2≤S ih)
